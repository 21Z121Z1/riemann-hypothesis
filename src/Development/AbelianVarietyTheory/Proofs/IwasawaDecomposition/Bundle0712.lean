import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0688
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0696
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariant
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

section Transfer

variable {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X]

theorem isCell_transfer {φ : InvFun O} (m1 m2 : Module O X) (f1 : letI := m1; Module.Finite O X)
    (f2 : letI := m2; Module.Finite O X)
    (hbal : ∀ β, β ∈ (letI := m1; balForms bar X) ↔ β ∈ (letI := m2; balForms bar X))
    (hφ : ∀ B : X → X → ℝ, (letI := m1; letI := f1; φ.eval X B) = (letI := m2; letI := f2; φ.eval X B))
    {k : ℕ} {γ : Fin k → LinearMap.BilinForm ℤ X} (h : letI := m1; letI := f1; IsCell bar φ γ) :
    letI := m2; letI := f2; IsCell bar φ γ := by
  obtain ⟨hm, hn, hl, hs⟩ := h
  have hZ : ∀ β : LinearMap.BilinForm ℤ X, (letI := m1; letI := f1; φ.evalZ β) = (letI := m2; letI := f2; φ.evalZ β) :=
    fun β => hφ _
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hs
  letI := m2
  letI := f2
  refine ⟨fun i => (hbal _).1 (hm i), hn, fun c hc => ?_, N, ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · rw [← hφ]
    simp only [← hZ]
    exact hl c hc
  · rw [← hZ]; exact h1 i
  · rw [← hZ]; exact h2 β ((hbal β).2 hβ) hp
  · exact h3 β ((hbal β).2 hβ) hp (by rw [hZ]; exact he)

theorem isStarDepth_transfer {ψ w : InvFun O} (m1 m2 : Module O X) (f1 : letI := m1; Module.Finite O X)
    (f2 : letI := m2; Module.Finite O X)
    (hbal : ∀ β, β ∈ (letI := m1; balForms bar X) ↔ β ∈ (letI := m2; balForms bar X))
    (hψ : ∀ B : X → X → ℝ, (letI := m1; letI := f1; ψ.eval X B) = (letI := m2; letI := f2; ψ.eval X B))
    (hw : ∀ B : X → X → ℝ, (letI := m1; letI := f1; w.eval X B) = (letI := m2; letI := f2; w.eval X B))
    {B₁ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {t : ℝ} (h : letI := m1; letI := f1; IsStarDepth bar ψ w B₁ t) :
    letI := m2; letI := f2; IsStarDepth bar ψ w B₁ t := by
  obtain ⟨ht, k, γ, v, hc, hv, hpos, hw1, hin, hB, hBt⟩ := h
  exact ⟨ht, k, γ, v, isCell_transfer bar m1 m2 f1 f2 hbal hψ hc, (hbal v).1 hv, hpos, (hw _).symm.trans hw1, hin, hB,
    hBt⟩

end Transfer

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem host_bar_map_comm (σ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E) : σ (H.bar a) = H.bar (σ a) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let s : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv σ
  have hs : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = s x := fun x =>
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x).symm
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, hs, hs, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact IsCMField.complexEmbedding_complexConj E (φ.comp s.toRingHom) _

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem mem_balForms_twist (τ : 𝓞 E ≃+* 𝓞 E) (β : LinearMap.BilinForm ℤ X) :
    β ∈ balForms H.bar X ↔ β ∈ (letI := Module.compHom X τ.toRingHom; balForms H.bar X) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    show β (τ a • y) z = β y (τ (H.bar a) • z)
    rw [h2, host_bar_map_comm]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    have := h2 (τ.symm a) y z
    change β (τ (τ.symm a) • y) z = β y (τ (H.bar (τ.symm a)) • z) at this
    rwa [host_bar_map_comm, τ.apply_symm_apply] at this

theorem eval_twist_of_isTwInv {φ : InvFun (𝓞 E)} (hφ : IsTwInv H φ) (τ : 𝓞 E ≃+* 𝓞 E) (hτ : τ H.w0 = H.w0)
    [Module.Finite (𝓞 E) X] (hf : letI := Module.compHom X τ.toRingHom; Module.Finite (𝓞 E) X) (B : X → X → ℝ) :
    φ.eval X B = (letI := Module.compHom X τ.toRingHom; letI := hf; φ.eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  rw [φ.eval_eq hr, ← hφ τ hτ]
  let g : (Fin n → 𝓞 E) →+ X := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => τ.symm (a i), funext fun i => τ.apply_symm_apply _⟩
  letI : Module (𝓞 E) X := Module.compHom _ τ.toRingHom
  letI := hf
  exact (φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _).symm

omit [Module (𝓞 E) X] in

theorem depthSet_twist_subset {ψ w : InvFun (𝓞 E)} (hψ : IsTwInv H ψ) (hw : IsTwInv H w) (σ : 𝓞 E ≃+* 𝓞 E)
    (hσ : σ H.w0 = H.w0) (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) :
    depthSet H.bar ψ w n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ⊆ depthSet H.bar ψ w n B := by
  rintro t ⟨X₁, i1, i2, i3, r, B₁, hr, hrad, hB, hd⟩
  set τ := σ.symm with hτdef
  have hτ : τ H.w0 = H.w0 := (σ.symm_apply_eq).2 hσ.symm
  let g : (Fin n → 𝓞 E) →+ X₁ := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => σ (a i), funext fun i => σ.symm_apply_apply _⟩
  have hgB : ∀ a b, B a b = B₁ (g a) (g b) := fun a b => by
    have := hB (fun i => τ (a i)) (fun i => τ (b i))
    simp only [hτdef, RingEquiv.apply_symm_apply] at this
    exact this
  have hf' : letI := Module.compHom X₁ τ.toRingHom; Module.Finite (𝓞 E) X₁ := by
    letI := Module.compHom X₁ τ.toRingHom
    exact Module.Finite.of_surjective (⟨g.toAddHom, hg⟩ : (Fin n → 𝓞 E) →ₗ[𝓞 E] X₁) hs
  have hd' := isStarDepth_transfer H.bar i2 (Module.compHom X₁ τ.toRingHom) i3 hf' (mem_balForms_twist H τ)
    (eval_twist_of_isTwInv H hψ τ hτ hf') (eval_twist_of_isTwInv H hw τ hτ hf') hd
  letI := Module.compHom X₁ τ.toRingHom
  exact ⟨X₁, i1, _, hf', ⟨g.toAddHom, hg⟩, B₁, hs, hrad, hgB, hd'⟩

theorem isTwInv_starDepth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ w : InvFun (𝓞 E)),
    IsTwInv H ψ → IsTwInv H w → IsTwInv H (starDepth H.bar ψ w) := by
  intro E _ _ _ H ψ w hψ hw σ hσ n B
  show sSup _ = sSup _
  congr 1
  refine Set.Subset.antisymm (depthSet_twist_subset H hψ hw σ hσ n B) ?_
  have h := depthSet_twist_subset H hψ hw σ.symm ((σ.symm_apply_eq).2 hσ.symm) n
    (fun a b => B (fun i => σ (a i)) (fun i => σ (b i)))
  simpa only [RingEquiv.apply_symm_apply] using h

end Twist

example {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (hψ : IsTwInv H ψ) :
    IsTwInv H (starDepth H.bar ψ (zeroFun (𝓞 E))) :=
  isTwInv_starDepth E H ψ _ hψ fun σ _ n B => by simp [zeroFun]

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuperadditiveOfCellsCoverCone
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.CoverSuper

theorem mul_evalR_le {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {e : X ≃ₗ[O] X} {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {c : Fin m → ℝ} (hγ : IsCell bar φ γ) (hc : ∀ i, 0 ≤ c i)
    (hB : pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) (f : X ≃ₗ[O] X) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hℓ : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (N : ℝ) * φ.evalZ β ≤ ℓ β) :
    (N : ℝ) * evalR φ B ≤ ∑ i, c i * (ℓ (pull (f.trans e.symm).toLinearMap (γ i)) : ℝ) ∧
      pullR f.toLinearMap B = ∑ i, c i • toReal (pull (f.trans e.symm).toLinearMap (γ i)) := by
  have hB' : ∀ a b, B (e a) (e b) = ∑ i, c i * (γ i a b : ℝ) := fun a b => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hB a b
  have hev : evalR φ B = ∑ i, c i * φ.evalZ (γ i) :=
    hγ.linear.eval_eq_sum (r := e.toLinearMap) e.surjective hc hB'
  refine ⟨?_, LinearMap.ext₂ fun a b => ?_⟩
  · rw [hev, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hℓ _ (pull_mem (f.trans e.symm).toLinearMap (hγ.mem i)) (fun y => hγ.nonneg i _)
    rw [evalZ_pull φ (f.trans e.symm).surjective] at h1
    calc (N : ℝ) * (c i * φ.evalZ (γ i)) = c i * (N * φ.evalZ (γ i)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (hc i)
  · have := hB' (e.symm (f a)) (e.symm (f b))
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [LinearMap.sum_apply, this]

theorem add_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ}
    (hB : B ∈ psdCone bar X) (hB' : B' ∈ psdCone bar X) : B + B' ∈ psdCone bar X := by
  obtain ⟨m₁, γ₁, c₁, h1, h2, h3, rfl⟩ := ConeSpan.exists_nonneg_comb_of_mem_psdCone O bar X B hB
  obtain ⟨m₂, γ₂, c₂, k1, k2, k3, rfl⟩ := ConeSpan.exists_nonneg_comb_of_mem_psdCone O bar X B' hB'
  have := ConeSub.sum_smul_toReal_mem_psdCone O bar X (m₁ + m₂) (Fin.append γ₁ γ₂) (Fin.append c₁ c₂)
    (fun i => Fin.addCases (fun j => by simpa using h1 j) (fun j => by simpa using k1 j) i)
    (fun i => Fin.addCases (fun j => by simpa using h2 j) (fun j => by simpa using k2 j) i)
    (fun i => Fin.addCases (fun j => by simpa using h3 j) (fun j => by simpa using k3 j) i)
  simpa [Fin.sum_univ_add] using this

theorem superadd_of_cover : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X],
    (∀ B ∈ psdCone bar X, ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      IsCell bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) →
    ∀ B ∈ psdCone bar X, ∀ B' ∈ psdCone bar X, evalR φ B + evalR φ B' ≤ evalR φ (B + B') := by
  intro O _ _ _ _ bar φ X _ _ _ hcov B hB B' hB'
  have hBB := add_mem_psdCone O bar X hB hB'
  obtain ⟨e₁, m₁, γ₁, c₁, hγ₁, hc₁, h₁⟩ := hcov B hB
  obtain ⟨e₂, m₂, γ₂, c₂, hγ₂, hc₂, h₂⟩ := hcov B' hB'
  obtain ⟨e₃, m₃, γ₃, c₃, hγ₃, hc₃, h₃⟩ := hcov (B + B') hBB
  obtain ⟨N, ℓ, hN, hℓ1, hℓ2, -⟩ := hγ₃.strict
  obtain ⟨i1, j1⟩ := mul_evalR_le hγ₁ hc₁ h₁ e₃ hℓ2
  obtain ⟨i2, j2⟩ := mul_evalR_le hγ₂ hc₂ h₂ e₃ hℓ2
  have hev3 : evalR φ (B + B') = ∑ i, c₃ i * φ.evalZ (γ₃ i) :=
    hγ₃.linear.eval_eq_sum (r := e₃.toLinearMap) e₃.surjective hc₃ fun a b => by
      simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h₃ a b
  have hN3 : (N : ℝ) * evalR φ (B + B') = ∑ i, c₃ i * (ℓ (γ₃ i) : ℝ) := by
    rw [hev3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hℓ1 i]; ring
  have hpull : pullR e₃.toLinearMap (B + B') = pullR e₃.toLinearMap B + pullR e₃.toLinearMap B' :=
    LinearMap.ext₂ fun a b => by simp
  have rel := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
    (β := Sum.elim (Sum.elim (fun i => pull (e₃.trans e₁.symm).toLinearMap (γ₁ i))
      (fun i => pull (e₃.trans e₂.symm).toLinearMap (γ₂ i))) γ₃)
    (c := Sum.elim (Sum.elim c₁ c₂) (-c₃)) (by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul,
        Finset.sum_neg_distrib]
      rw [← j1, ← j2, ← h₃, hpull]
      abel)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at rel
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : (N : ℝ) * (evalR φ B + evalR φ B') ≤ N * evalR φ (B + B') := by
    rw [mul_add, hN3]
    linarith
  exact le_of_mul_le_mul_left key hNpos

end GlobalTheory.PolFan.CoverSuper
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsGlobalConditions
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan.PhiOrder

theorem lift_trait {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ}
    (ξ : Sp (ChartRing k m e) ⟶ gen Y) (hξ : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (χ : Sp W ⟶ Y.X)
    (hχ : χ (closedPoint W) = genι Y (ξ (closedPoint _))) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : ChartRing k m e →+* V),
      CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y :=
  GlobalTheory.T.exists_dvr_lift_through_etale_chart Y ξ hξ W hW χ hχ

theorem form_compare {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ}
    (ξ : Sp (ChartRing k m e) ⟶ gen Y) {tC : SAB H (Sp (ChartRing k m e))} (mC : SABMap tC Y.t (ξ ≫ genι Y))
    (PC : PELUnif (maximalIdeal (ChartRing k m e)) tC) (γ : Fin m → LinearMap.BilinForm ℤ PC.D.toPre.X)
    (hγ : IsMonomial PC.D.toPre (bdParam k m e) γ)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (ϖ : W) (hϖ : Irreducible ϖ)
    (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (mχ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t)
    (hr : Set.range (jK W ≫ χ) ⊆ Set.range Y.j) (be : LinearMap.BilinForm ℤ P.D.toPre.X)
    (hbe : IsMonomial P.D.toPre ![ϖ] ![be])
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (ϖ' : V) (hϖ' : Irreducible ϖ')
    (f : W →+* V) (ψ : ChartRing k m e →+* V) (hf : Function.Injective f) [hfl : IsLocalHom f] [hψl : IsLocalHom ψ]
    (hc : spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y) (r : ℕ) (u : Vˣ) (hu : f ϖ = u * ϖ' ^ r)
    (n : Fin m → ℕ) (v : Fin m → Vˣ) (hv : ∀ i, ψ (bdParam k m e i) = v i * ϖ' ^ n i) :
    ∃ ε : P.D.toPre.X ≃ₗ[𝓞 E] PC.D.toPre.X, ∀ y, (r : ℤ) * be y y = ∑ i, (n i : ℤ) * γ i (ε y) (ε y) :=
  GlobalTheory.T.monomial_form_on_chart_ring Y ξ mC PC γ hγ W hW ϖ hϖ χ t mχ P hr be hbe V hV ϖ' hϖ' f ψ hf hfl hψl hc r u hu n v hv

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem comb_evalZ (ψ φ : InvFun (𝓞 E)) (d : ℕ) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    (be : LinearMap.BilinForm ℤ X) : (comb 0 ψ d φ).evalZ be = d * φ.evalZ be := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  unfold InvFun.evalZ
  rw [InvFun.eval_eq _ hr, InvFun.eval_eq _ hr]
  show (0 : ℕ) * ψ.toFun n _ + d * φ.toFun n _ = _
  simp

theorem eq_of_diag {X : Type} [AddCommGroup X] (B₁ B₂ : LinearMap.BilinForm ℤ X) (h₁ : ∀ y z, B₁ y z = B₁ z y)
    (h₂ : ∀ y z, B₂ y z = B₂ z y) (h : ∀ y, B₁ y y = B₂ y y) (y z : X) : B₁ y z = B₂ y z := by
  have e1 := h (y + z)
  simp only [map_add, LinearMap.add_apply] at e1
  rw [h y, h z, h₁ z y, h₂ z y] at e1
  omega

theorem range_j_subset_abLocus {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨w, rfl⟩
  have hw : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact ⟨w, rfl⟩
  show (Y.jQ ≫ pullback.fst _ _) w ∈ _
  rw [Scheme.Hom.comp_apply]
  exact hw

end SlopeTestRemainingChoices

section Cases

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem order_of_abelian (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (φ : InvFun (𝓞 E))
    (hsupp : ∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (ϖ : W)
    (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (mχ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t)
    (be : LinearMap.BilinForm ℤ P.D.toPre.X) (hab : χ (closedPoint W) ∈ abLocus Y.t.G) :
    ∃ n : ℕ, (n : ℝ) = φ.evalZ be ∧ idlAlong BD.idealSheaf χ = Ideal.span {ϖ ^ n} := by
  obtain ⟨h₁, h₂, h₃⟩ := hW
  let T : CDVR := { V := W }
  have hc : (closedPoint T.V : Sp T.V) ∈ abLocus t.G :=
    (abLocus_pullback abLocusOne Y.t.semi mχ.cart.1 _).1 hab
  have hs : Subsingleton P.D.toPre.X := (closed_mem_abLocus_iff T P).1 hc
  refine ⟨0, ?_, ?_⟩
  · rw [InvFun.evalZ, φ.eval_of_subsingleton]; simp
  · have hns : χ (closedPoint W) ∉ BD.idealSheaf.support := fun h => hsupp _ h hab
    have htop : FinalTheorems.stalkId BD.idealSheaf (χ (closedPoint W)) = ⊤ := by
      by_contra h
      exact hns ((mem_support_iff_stalkId _ _).2 h)
    rw [pow_zero, Ideal.span_singleton_one, idlAlong, htop, Ideal.map_top]

end Cases

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem order_of_chart (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d : ℕ)
    (x : gen Y) (hch : GlobalTheory.MumfordChart.HasChartOf φ Y BD d x)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (ϖ : W) (hϖ : Irreducible ϖ)
    (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (mχ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t)
    (hr : Set.range (jK W ≫ χ) ⊆ Set.range Y.j) (be : LinearMap.BilinForm ℤ P.D.toPre.X)
    (hbe : ∀ y z, be y z = be z y) (hmon : IsMonomial P.D.toPre ![ϖ] ![be])
    (hx : χ (closedPoint W) = genι Y x) :
    ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong BD.idealSheaf χ = Ideal.span {ϖ ^ n} := by
  obtain ⟨k, _, m, e, ξ, tC, PC, γ, δ, a, hξx, h₁, -, h₃, ⟨mC⟩, h₅, -, hcone, hγδ, ha, hid⟩ := hch
  have := hW.1
  obtain ⟨V, _, _, _, f, ψ, hV, hfi, hfl, hψl, hcomm⟩ := lift_trait Y ξ h₁ W hW χ (by rw [hx, hξx])
  have := hV.1
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hfϖ : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hfi (h.trans (map_zero f).symm))
  obtain ⟨r, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfϖ hϖ'

  have hψt : ∀ i, ψ (bdParam k m e i) ≠ 0 := by
    let q : Sp V := ⟨⊥, Ideal.isPrime_bot⟩
    have hq : spMap f q = (⟨⊥, Ideal.isPrime_bot⟩ : Sp W) :=
      PrimeSpectrum.ext (Ideal.comap_bot_of_injective f hfi)
    have hw : (⟨⊥, Ideal.isPrime_bot⟩ : Sp W) = jK W (⟨⊥, Ideal.isPrime_bot⟩ : Sp (FractionRing W)) :=
      PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (IsFractionRing.injective W (FractionRing W))).symm
    have e1 : χ (spMap f q) = genι Y (ξ (spMap ψ q)) := by
      rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    have hab : genι Y (ξ (spMap ψ q)) ∈ abLocus Y.t.G := by
      rw [← e1, hq, hw]
      exact range_j_subset_abLocus Y (hr ⟨_, Scheme.Hom.comp_apply (jK W) χ _⟩)
    have hnb : ξ (spMap ψ q) ∉ genBd Y := fun h => (mem_genBd_iff.1 h) hab
    have hp : ∏ i, bdParam k m e i ∉ (spMap ψ q).asIdeal := fun h => hnb ((h₃ _).2 h)
    have hp' : ψ (∏ i, bdParam k m e i) ≠ 0 := fun h => hp (by
      show ψ (∏ i, bdParam k m e i) ∈ (⊥ : Ideal V)
      rw [h]; exact Ideal.zero_mem _)
    rw [map_prod] at hp'
    exact fun i => Finset.prod_ne_zero_iff.1 hp' i (Finset.mem_univ i)
  choose nn vv hvv using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hψt i) hϖ'
  obtain ⟨ε, hε⟩ := form_compare Y ξ mC PC (fun i => (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) h₅ W hW ϖ hϖ χ t mχ P
    hr be hmon V hV ϖ' hϖ' f ψ hfi hcomm r u hu nn vv hvv

  have hU : IsUnit (∏ i, (vv i : V) ^ a i) := by
    have := (∏ i, vv i ^ a i).isUnit
    push_cast at this
    exact this
  have hmapψ : idlAlong BD.idealSheaf (spMap f ≫ χ) = Ideal.span {ϖ' ^ ∑ i, nn i * a i} := by
    rw [hcomm, GlobalTheory.TraitOrder.idlAlong_comp, hid, Ideal.map_span, Set.image_singleton, map_prod]
    simp_rw [map_pow, hvv, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
    exact Ideal.span_singleton_mul_left_unit hU _
  have hmapf : (idlAlong BD.idealSheaf χ).map f = Ideal.span {ϖ' ^ ∑ i, nn i * a i} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp]; exact hmapψ
  have hne : idlAlong BD.idealSheaf χ ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hmapf
    exact pow_ne_zero _ hϖ'.ne_zero (Ideal.span_singleton_eq_bot.1 hmapf.symm)
  obtain ⟨n0, hn0⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hrN : r * n0 = ∑ i, nn i * a i := by
    rw [hn0, Ideal.map_span, Set.image_singleton, map_pow, hu, mul_pow, ← pow_mul,
      Ideal.span_singleton_mul_left_unit (u.isUnit.pow _)] at hmapf
    have hass := (Ideal.span_singleton_eq_span_singleton.1 hmapf)
    exact le_antisymm ((pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 hass.dvd)
      ((pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 hass.symm.dvd)
  refine ⟨n0, ?_, hn0⟩

  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    exact hϖ.not_isUnit (isUnit_of_map_unit f ϖ (hu ▸ u.isUnit))
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  let εZ : P.D.toPre.X →ₗ[ℤ] PC.D.toPre.X := ε.toLinearMap.toAddMonoidHom.toIntLinearMap
  let B₂ : LinearMap.BilinForm ℤ P.D.toPre.X :=
    ∑ i, (nn i : ℤ) • (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X).compl₁₂ εZ εZ
  have hB₂ : ∀ y z, B₂ y z = ∑ i, (nn i : ℤ) * (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X) (ε y) (ε z) := by
    intro y z
    simp [B₂, εZ, LinearMap.sum_apply]
  have hfull : ∀ y z, (r : ℤ) * be y z = ∑ i, (nn i : ℤ) * (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X) (ε y) (ε z) := by
    intro y z
    have := eq_of_diag ((r : ℤ) • be) B₂ (fun y z => by simp [hbe y z])
      (fun y z => by rw [hB₂, hB₂]; exact Finset.sum_congr rfl fun i _ => by rw [(γ i).2.1])
      (fun y => by rw [hB₂, ← hε y]; simp) y z
    rw [hB₂] at this
    simpa using this
  have hlin : φ.LinearOn (fun i => (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) := by
    have e' : (fun i => (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) = fun i => (l.M' : ℤ) • δ i := funext hγδ
    rw [e']; exact hcone.linearOn_smul l.M'
  have hφbe : φ.evalZ be = ∑ i, ((nn i : ℝ) / r) * φ.evalZ (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X) := by
    rw [← hlin (fun i => (nn i : ℝ) / r) (fun i => by positivity), ← φ.eval_equiv ε]
    unfold InvFun.evalZ
    congr 1
    funext y z
    have h := congrArg (fun n : ℤ => (n : ℝ)) (hfull y z)
    push_cast at h
    rw [eq_comm, ← mul_right_inj' hr', Finset.mul_sum, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have hN : (r : ℝ) * n0 = ∑ i, (nn i : ℝ) * (d * φ.evalZ (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hrN
    push_cast at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [ha]
  rw [hφbe, ← mul_right_inj' hr', hN, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

end Chart

theorem isPhiDiv_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (φ : InvFun (𝓞 E)), IsPolFan H.bar (min D.p D.q) φ →
    NoSelfInt H.bar (min D.p D.q) φ → ∀ (Y : Model Xo c (RingHom.id c.F)) (BD : GlobalTheory.EffCartierData Y.X) (d : ℕ),
    SmoothOfRelativeDimension D.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) →
    (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) → (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) →
    IsPhiDiv (comb 0 φ d φ) Y BD := by
  intro E _ _ _ H D l Xo c φ _ _ Y BD d _ _ hsupp hch W _ _ _ hW ϖ hϖ χ t mχ P hr be hbe hmon
  by_cases hab : χ (closedPoint W) ∈ abLocus Y.t.G
  · exact order_of_abelian Y BD _ hsupp W hW ϖ χ t mχ P be hab
  · rcases GlobalTheory.GenFan.exists_of_id Y (χ (closedPoint W)) with ⟨x, hxb, hxz⟩ | hj
    · obtain ⟨n, hn, hI⟩ := order_of_chart φ Y BD d x (hch x hxb) W hW ϖ hϖ χ t mχ P hr be hbe.1 hmon hxz.symm
      exact ⟨n, hn.trans (comb_evalZ φ φ d be).symm, hI⟩
    · exact absurd (range_j_subset_abLocus Y hj) hab

end GlobalTheory.GenFan.PhiOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTwoFactorSqValuesCorrespondStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightTwoFactor_sq_values_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → ∀ (y : D'.toPre.X) (z : (DegPre.BF D.toPre (FractionRing R)).left) (J : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((DegPre.BF D.toPre (FractionRing R)).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → IsDomain ((DegPre.BF D.toPre (FractionRing R)).left.presheaf.stalk z) → sval (f 0) (DegPre.prB D.toPre (FractionRing R)).left z J ≠ 0 → val (DegPre.famMult D'.toPre (FractionRing R) 2 (2 • y) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J' ^ 2 = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre (DegPre.BF D.toPre (FractionRing R)) (2 • y)).left * (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (1 : (DegPre.BF D.toPre (FractionRing R)) ⟶ D'.toPre.P.A).left)⁻¹) ^ 2 * val (DegPre.famMult D.toPre (FractionRing R) 2 (xe (2 • y)) 0) (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z J ^ 2 := by
  first | exact @GlobalTheory.PsiCompare.famMult_sq_corr | exact GlobalTheory.PsiCompare.famMult_sq_corr | (intros; apply GlobalTheory.PsiCompare.famMult_sq_corr <;> assumption)
end

