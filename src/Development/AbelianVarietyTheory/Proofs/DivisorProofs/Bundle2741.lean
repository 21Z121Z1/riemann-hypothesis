import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFamilyDeriv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetFam

open TrivSqZeroExt in
theorem dual_unit {a a' : ℂ} (ha : a ≠ 0) : IsUnit (inl a + inr a' : DualNumber ℂ) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simpa using ha

open TrivSqZeroExt in
theorem dual_mul {S V : DualNumber ℂ} {a a' r r' p p' e : ℂ} {k : ℕ} (ha : a ≠ 0) (hr : r ≠ 0)
    (h1 : S * inl a * (inl r + inr r') = (inl p + inr p') * (inl r + inr r') ^ k * (inl a + inr a') * inl r)
    (h2 : V * (inl a + inr a') * inl r = (1 + inr e) * inl a * (inl r + inr r')) :
    (S * V).fst / r ^ k = p ∧ (S * V).snd / r ^ k = p' + e * p + k * (r' / r) * p := by
  have ua : IsUnit (inl a : DualNumber ℂ) := by simpa using dual_unit (a' := 0) ha
  have ur : IsUnit (inl r : DualNumber ℂ) := by simpa using dual_unit (a' := 0) hr
  have hu := ((ua.mul (dual_unit (a' := r') hr)).mul (dual_unit (a' := a') ha)).mul ur
  have key : S * V = (inl p + inr p') * (inl r + inr r') ^ k * (1 + inr e) := by
    apply hu.mul_right_cancel
    linear_combination (V * (inl a + inr a') * inl r) * h1 +
      ((inl p + inr p') * (inl r + inr r') ^ k * (inl a + inr a') * inl r) * h2
  rw [key]
  constructor
  · simp [hr]
  · rcases k with _ | k
    · simp; ring
    · simp [TrivSqZeroExt.snd_pow]
      field_simp
      ring

open TrivSqZeroExt in
theorem dual_zero {V : DualNumber ℂ} {a r e : ℂ} (ha : a ≠ 0) (hr : r ≠ 0)
    (h2 : V * (inl a + inr 0) * inl r = (1 + inr e) * inl a * (inl r + inr 0)) : V = 1 + inr e := by
  have ua : IsUnit (inl a : DualNumber ℂ) := by simpa using dual_unit (a' := 0) ha
  have ur : IsUnit (inl r : DualNumber ℂ) := by simpa using dual_unit (a' := 0) hr
  apply (ua.mul ur).mul_right_cancel
  rw [inr_zero, add_zero, add_zero] at h2
  linear_combination h2

variable {g' r g : ℕ} (σ : Fin g ≃ Fin g' ⊕ Fin r)

def join (z : Fin g' → ℂ) (t : Fin r → ℂ) : Fin g → ℂ := fun j => Sum.elim z t (σ j)

theorem leftComponent_join (z : Fin g' → ℂ) (t : Fin r → ℂ) : zP σ (join σ z t) = z := by
  funext i; simp [zP, join]

theorem secondBlock_join (z : Fin g' → ℂ) (t : Fin r → ℂ) : tP σ (join σ z t) = t := by
  funext i; simp [tP, join]

theorem join_zero : join σ 0 0 = 0 := by
  funext j; simp only [join]; rcases σ j with i | i <;> simp

theorem diff_join : Differentiable ℂ fun z : Fin g' → ℂ => join σ z 0 := by
  refine differentiable_pi.2 fun j => ?_
  simp only [join]
  rcases σ j with i | i
  · simp only [Sum.elim_inl]; fun_prop
  · simp

def zL : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ.symm (Sum.inl i))

def tL (c : ℂ) (v : Fin r → ℂ) : (Fin g → ℂ) →L[ℂ] ℂ :=
  c • ∑ l, v l • ContinuousLinearMap.proj (σ.symm (Sum.inr l))

theorem zL_apply (Y : Fin g → ℂ) : zL σ Y = zP σ Y := rfl

theorem tL_apply (c : ℂ) (v : Fin r → ℂ) (Y : Fin g → ℂ) : tL σ c v Y = c * (v ⬝ᵥ tP σ Y) := by
  simp [tL, tP, dotProduct]

theorem fderiv_eq (c : ℂ) (v : Fin r → ℂ) {F : (Fin g → ℂ) → ℂ} {φ : (Fin g' → ℂ) → ℂ} (hφ : Differentiable ℂ φ)
    (h : ∀ Y, F Y = Complex.exp (c * (v ⬝ᵥ tP σ Y)) * φ (zP σ Y)) (Z : Fin g → ℂ) :
    fderiv ℂ F 0 Z = fderiv ℂ φ 0 (zP σ Z) + c * (v ⬝ᵥ tP σ Z) * φ 0 := by
  have e : F = fun Y => Complex.exp (tL σ c v Y) * φ (zL σ Y) := by
    funext Y; rw [h, tL_apply, zL_apply]
  have h1 : HasFDerivAt (fun Y => Complex.exp (tL σ c v Y)) _ (0 : Fin g → ℂ) := (tL σ c v).hasFDerivAt.cexp
  have h2 : HasFDerivAt (fun Y => φ (zL σ Y)) _ (0 : Fin g → ℂ) :=
    (hφ (zL σ 0)).hasFDerivAt.comp (0 : Fin g → ℂ) (zL σ).hasFDerivAt
  have h3 := (h1.mul h2).fderiv
  rw [e]
  refine (congrArg (fun L => L Z) h3).trans ?_
  rw [map_zero, map_zero]
  simp [tL_apply, zL_apply, mul_comm]

end GlobalTheory.MBLow.Cl.JetFam

namespace GlobalTheory.MBLow.Cl

open JetFam

theorem jet_family_deriv : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g' r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) (_ : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g' → ℂ), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b → ∃ (Z : Fin g → ℂ) (c₀ : ℂ), zP σ Z = W ∧ (W = 0 → ∀ χ, vE (gm.s (ν.eX χ)) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ tP σ Z))) ∧ ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (F : (Fin g → ℂ) → ℂ), ν.FamV s f → Differentiable ℂ F → (∀ Y h, d.IsPt σ Y h → f α h.b * h.s α = (d.fr (zP σ Y) : ℂ) ^ k * F Y) → (jc ν s gm α).fst / ν.rg ^ k = F 0 ∧ (jc ν s gm α).snd / ν.rg ^ k = fderiv ℂ F 0 Z + k * c₀ * F 0 := by
  intro R _ _ _ _ D hE hT _ N ν g' r g bX d σ G gm W ho hW
  obtain ⟨T, hT'⟩ := GlobalTheory.T.torusExtension_tangent_generators_holomorphicFrame R D hE hT N ν g' r bX d G gm W ho hW
  have hrg : ν.rg ≠ 0 := GlobalTheory.Ex.FamVal.rg_ne ν
  have hne : ∀ z, G.frG (ν.J (ν.eA (d.ex z)).left) z ≠ 0 := fun z => by
    rw [← G.fr_eq]; exact mul_ne_zero (Units.ne_zero _) hrg
  have h0 : G.frG (ν.J (ν.eA (d.ex 0)).left) 0 = ν.rg := by
    rw [← G.fr_eq, d.fr_zero]; simp
  refine ⟨join σ W T, fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / ν.rg, leftComponent_join σ W T, ?_, ?_⟩
  · intro hW0 χ
    have := hT' χ _ rfl
    subst hW0
    rw [map_zero, map_zero] at this
    rw [secondBlock_join]
    exact dual_zero (hne _) (hne _) this
  · intro k s f α F hs hF hf
    obtain ⟨o, hz, hp⟩ := ho
    have hb : redE ℂ ≫ gm.b.left = (DegPre.zeroF D ℂ).left := by
      rw [← hz.1]; exact hp.1.symm
    have hpt := fun Y => ((GlobalTheory.MBLow.Cl.exp_onto_torusExt N g' r g bX d σ).1 Y).exists
    have hφ : Differentiable ℂ fun z => F (join σ z 0) := hF.comp (diff_join σ)
    have hA : ∀ z, f α (d.ex z) * d.fr (d.t12 *ᵥ co bX α) * d.fr z =
        F (join σ z 0) * (d.fr z : ℂ) ^ k * d.fr (d.t12 *ᵥ co bX α + z) := fun z => by
      obtain ⟨h, hh⟩ := hpt (join σ z 0)
      have e1 := hf _ h hh
      have e2 := hh.2 α
      rw [hh.1] at e1
      rw [leftComponent_join] at e1 e2
      rw [secondBlock_join] at e2
      simp only [dotProduct_zero, mul_zero, Complex.exp_zero, one_mul] at e2
      linear_combination (d.fr (d.t12 *ᵥ co bX α + z) : ℂ) * e1 - f α (d.ex z) * e2
    have hB : ∀ Y, F Y = Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (co bX α ⬝ᵥ tP σ Y)) * F (join σ (zP σ Y) 0) :=
      fun Y => by
      obtain ⟨h, hh⟩ := hpt Y
      have e1 := hf _ h hh
      have e2 := hh.2 α
      have e3 := hA (zP σ Y)
      rw [hh.1] at e1
      apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero k (d.fr (zP σ Y)).ne_zero)
        (d.fr (d.t12 *ᵥ co bX α + zP σ Y)).ne_zero)
      linear_combination (-(d.fr (d.t12 *ᵥ co bX α + zP σ Y) : ℂ)) * e1 + f α (d.ex (zP σ Y)) * e2 +
        Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (co bX α ⬝ᵥ tP σ Y)) * e3
    have h1 := GlobalTheory.T.familyMember_tangentValue_eq_firstJet R D hE hT N ν g' d.toAB G gm.b W hb hW k s f α _ _ hs (d.c_eq α) hφ hA
    have h2 := dual_mul (hne _) (hne _) h1 (hT' α _ rfl)
    rw [h0, join_zero] at h2
    rw [fderiv_eq σ _ _ hφ hB, leftComponent_join, secondBlock_join, join_zero]
    exact h2

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFamilyPullbackFirst
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatJet.BaseChangeFil

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Type} [Fintype I] {n : ℕ}

theorem repr_algebraMap (J : JetRing R I n) (r : R) :
    J.b.repr (algebraMap R J.B r) = Finsupp.single ⟨0, by simp⟩ r := by
  rw [Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_single_one]

theorem map_algebraMap (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) (r : R) :
    τ (algebraMap R J.B r) = algebraMap R' J'.B (σ r) := by
  refine J'.b.ext_elem fun ν ↦ ?_
  rw [hτ, repr_algebraMap, repr_algebraMap, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

theorem map_t (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) (i : I) : τ (J.t i) = J'.t i := by
  refine J'.b.ext_elem fun ν ↦ ?_
  rw [hτ, JetRing.t, JetRing.t, Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

theorem π_surjective (J : JetRing R I n) : Function.Surjective J.π := fun r ↦
  ⟨algebraMap R J.B r, by rw [J.π_eq, repr_algebraMap, Finsupp.single_eq_same]⟩

theorem comp_π (σ : R →+* R') (J : JetRing R I n) (J' : JetRing R' I n) (τ : J.B →+* J'.B)
    (hτ : ∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) : σ.comp J.π = J'.π.comp τ :=
  RingHom.ext fun x ↦ by simp only [RingHom.comp_apply, J.π_eq, J'.π_eq, hτ]

end GlobalTheory.LatJet.BaseChangeFil

open GlobalTheory.LatJet.BaseChangeFil in

theorem GlobalTheory.LatJet.baseChange_liftFil : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (J' : JetRing R' I n) {X₀ : Obj F 𝔠 (Sp R)} {δ₀ : X₀.DetGen}
    {N : I → Module.End R (HdR X₀.A)} (Y : Family J X₀ δ₀ N) {X₁ : Obj F 𝔠 (Sp R')}
    {N₁ : I → Module.End R' (HdR X₁.A)} {p : X₁.A.left ⟶ X₀.A.left}, X₁.IsPullBy X₀ (spMap σ) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 R') (𝟙 _) X₁.A σ (spMap σ) p),
    (∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (N₁ i x)) → ∀ (τ : J.B →+* J'.B),
    (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) → IsDPMorphism J.κ J'.κ τ →
    ∀ {Z' : Obj F 𝔠 (Sp J'.B)} {q : Z'.A.left ⟶ Y.X'.A.left}, Z'.IsPullBy Y.X' (spMap τ) q →
    ∀ {i' : X₁.A.left ⟶ Z'.A.left} (hi' : X₁.IsPullBy Z' (spMap J'.π) i'), i' ≫ q = p ≫ Y.i →
    ∀ (mor' : GrpMor (dp0 R') (𝟙 _) X₁.A J'.κ (spMap J'.π) X₁.A (algebraMap R' J'.B) (𝟙 _) (Over.Hom.left (𝟙 X₁.A))),
    ∀ x ∈ Fil X₁.A, ∀ d, IsJetElt J' X₁ N₁ mor' x d → d ∈ liftFil J'.κ hi'.grp := by
  intro hAb F _ _ 𝔠 R R' _ _ σ I _ n J J' X₀ δ₀ N Y X₁ N₁ p hp m hN τ hτ hτdp Z' q hq i' hi' hiq mor'
  have hbc0 := GlobalTheory.T.jet_morphism_is_base_change hAb J X₀ Y.mor
  have hbc1 := GlobalTheory.T.jet_morphism_is_base_change hAb J' X₁ mor'
  have hspan := GlobalTheory.T.lie_filtration_spanned_correspondence hAb σ hp m
  have hb : spMap σ ≫ spMap J.π = spMap J'.π ≫ spMap τ := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp, comp_π σ J J' τ hτ]
  have M : GrpMor J.κ (spMap J.π) X₀.A J'.κ (spMap J'.π) X₁.A τ (spMap σ) p :=
    GrpMor.of_isGrpPullback hτdp hb hp.grp
  have nq : GrpMor (dp0 J.B) (𝟙 _) Y.X'.A (dp0 J'.B) (𝟙 _) Z'.A τ (spMap τ) q :=
    GrpMor.of_isGrpPullback (Cris.isDPMorphism_of_eq_bot _ rfl _ _) (by simp) hq.grp
  have hspanq := GlobalTheory.T.lie_filtration_spanned_correspondence hAb τ hq nq

  have hprim : ∀ c, c ∈ Submodule.span R' (Set.range m.pull) := by
    letI := σ.toAlgebra
    have hbc := (hAb.2.2.1 R X₀.A _ X₀.ab X₀.dim R' X₁.A p hp.grp).1
    intro c
    obtain ⟨z, rfl⟩ := hbc.2 c
    induction z with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul r c₀ => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c₀, rfl⟩)
  have key : ∀ x₀ ∈ Fil X₀.A, ∀ x, m.Corr x₀ x →
      ∃ d ∈ liftFil J'.κ hi'.grp, IsJetElt J' X₁ N₁ mor' x d := by
    intro x₀ hx₀ x hx
    obtain ⟨e0, he0⟩ := hbc0.exists x₀
    choose e he using fun i ↦ hbc0.exists (N i x₀)
    have hd₀ : IsJetElt J X₀ N Y.mor x₀ (e0 + ∑ i, J.t i • e i) := fun c ↦ by
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, he0 c, fun i ↦ he i c]
    have hd₀F := Y.fil x₀ hx₀ _ hd₀
    obtain ⟨d', hd'⟩ := GlobalTheory.T.nilpotent_divided_powers_compatible hAb J.κ J'.κ J.nil J'.nil J.π J'.π (π_surjective J)
      (π_surjective J') rfl rfl τ σ Y.pull hi' hq hiq M (e0 + ∑ i, J.t i • e i)
    refine ⟨d', hspanq.2.2 _ _ hd₀F (crysToDR_corr J.κ Y.pull.grp hi'.grp M nq hiq hd'), ?_⟩
    intro c
    induction hprim c using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨c₀, rfl⟩ := hc
      have e1 : mor'.pull (m.pull c₀) = M.pull (Y.mor.pull c₀) :=
        (GrpMor.pull_pull m mor' (m.comp mor') (fun _ ↦ rfl) rfl c₀).trans
          (GrpMor.pull_pull Y.mor M (m.comp mor') (fun r ↦ map_algebraMap σ J J' τ hτ r)
            (by simp) c₀).symm
      rw [e1, hd', hd₀ c₀, hx c₀]
      simp only [map_add, map_sum, map_mul, map_algebraMap σ J J' τ hτ, map_t σ J J' τ hτ,
        fun i ↦ hN i x₀ x hx c₀]
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [map_add, ha, hb, Finset.sum_add_distrib, mul_add]
      ring
    | smul r a _ ha =>
      simp only [map_smulₛₗ, LinearMap.map_smul, smul_eq_mul, ha, map_mul, mul_add, Finset.mul_sum,
        RingHom.id_apply]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
  intro x hx d hd
  have hP : ∀ x ∈ Submodule.span R' {x' | ∃ x₀ ∈ Fil X₀.A, m.Corr x₀ x'},
      ∃ d ∈ liftFil J'.κ hi'.grp, IsJetElt J' X₁ N₁ mor' x d := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨x₀, hx₀, hc⟩ := h
      exact key x₀ hx₀ x hc
    | zero => exact ⟨0, zero_mem _, fun c ↦ by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      refine ⟨a + b, add_mem ha hb, fun c ↦ ?_⟩
      simp only [LinearMap.add_apply, ha' c, hb' c, map_add, Finset.sum_add_distrib, mul_add]
      ring
    | smul r x _ hx =>
      obtain ⟨a, ha, ha'⟩ := hx
      refine ⟨algebraMap R' J'.B r • a, Submodule.smul_mem _ _ ha, fun c ↦ ?_⟩
      simp only [LinearMap.smul_apply, ha' c, map_smul, smul_eq_mul, map_mul, mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
  obtain ⟨d', hd'F, hd'⟩ := hP x (hspan.2.1 hx)
  have h0 : mor'.Corr 0 (d - d') := fun c ↦ by
    rw [LinearMap.sub_apply, hd c, hd' c, sub_self, LinearMap.zero_apply, map_zero]
  have h00 : mor'.Corr 0 0 := fun c ↦ by simp
  rw [sub_eq_zero.1 (hbc1.unique h0 h00)]
  exact hd'F
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberQuotientBounds
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.NumPt

theorem jet_real {f m r t b g dF R : ℝ} (hf0 : 0 ≤ f) (hm0 : 0 ≤ m) (hr0 : 0 ≤ r) (hd0 : 0 ≤ dF)
    (ht : 11 ≤ t) (hf : f ≤ t) (hm : m ≤ t) (hr : r ≤ t) (hb : t ^ 7 ≤ b) (hd : dF ≤ f * r * (2 * (2 * b) + 1))
    (hR : R ≤ b) (hg : b ^ 8 ≤ g) :
    4 * dF + 4 ≤ g ∧ dF * (2 * Real.sqrt (2 * f * m)) < g ∧
      R * (2 * f * m) ^ 3 * (r * (2 * f * m) / 4 + 2 * dF ^ 2) / g ≤ 1 / 2500 := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hp : ∀ n : ℕ, n ≤ 7 → t ^ n ≤ b := fun n hn => (pow_le_pow_right₀ ht1 hn).trans hb
  have h100 : 100 ≤ b := by nlinarith [hp 2 (by norm_num)]
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hfr : f * r ≤ t ^ 2 := by rw [sq]; exact mul_le_mul hf hr hr0 (by linarith)
  have hfm : f * m ≤ t ^ 2 := by rw [sq]; exact mul_le_mul hf hm hm0 (by linarith)
  have ht2 : 0 ≤ t ^ 2 := by positivity
  have h5 : 5 * t ^ 2 ≤ b := by
    have : t ^ 3 = t * t ^ 2 := by ring
    nlinarith [hp 3 (by norm_num)]
  have hdb : dF ≤ b ^ 2 := by
    have h1 : f * r * (2 * (2 * b) + 1) ≤ t ^ 2 * (5 * b) := mul_le_mul hfr (by linarith) (by linarith) ht2
    nlinarith
  have hN0 : 0 ≤ 2 * f * m := by positivity
  have hN : 2 * f * m ≤ b := by nlinarith
  have hN3 : (2 * f * m) ^ 3 ≤ b := by
    have h1 : (2 * f * m) ^ 3 ≤ (2 * t ^ 2) ^ 3 := pow_le_pow_left₀ hN0 (by linarith) 3
    have h2 : t ^ 7 = t * t ^ 6 := by ring
    have h3 : (2 * t ^ 2) ^ 3 = 8 * t ^ 6 := by ring
    have h4 : 0 ≤ t ^ 6 := by positivity
    nlinarith
  have hrb : r ≤ b := hr.trans (by simpa using hp 1 (by norm_num))
  have hs : Real.sqrt (2 * f * m) ≤ b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hq : ∀ n : ℕ, 100 * b ^ n ≤ b ^ (n + 1) := fun n => by
    rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_left h100 (by positivity)
  have e2 : 1 ≤ b ^ 2 := one_le_pow₀ hb1
  have q2 := hq 2
  have q3 := hq 3
  have q4 := hq 4
  have q5 := hq 5
  have q6 := hq 6
  have q7 := hq 7
  norm_num at q2 q3 q4 q5 q6 q7
  refine ⟨by linarith, ?_, ?_⟩
  · have h1 : dF * (2 * Real.sqrt (2 * f * m)) ≤ b ^ 2 * (2 * b) :=
      mul_le_mul hdb (by linarith) (by positivity) (by positivity)
    have h2 : b ^ 2 * (2 * b) = 2 * b ^ 3 := by ring
    linarith
  · rw [div_le_iff₀ (by linarith)]
    have h1 : r * (2 * f * m) ≤ b ^ 2 := by rw [sq]; exact mul_le_mul hrb hN hN0 (by linarith)
    have h2 : dF ^ 2 ≤ b ^ 4 := by
      have := pow_le_pow_left₀ hd0 hdb 2
      rwa [← pow_mul] at this
    have h3 : R * (2 * f * m) ^ 3 ≤ b * b := mul_le_mul hR hN3 (by positivity) (by linarith)
    have h4 : R * (2 * f * m) ^ 3 * (r * (2 * f * m) / 4 + 2 * dF ^ 2) ≤ b * b * (3 * b ^ 4) :=
      mul_le_mul h3 (by linarith) (by positivity) (by positivity)
    have h5 : b * b * (3 * b ^ 4) = 3 * b ^ 6 := by ring
    linarith

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := D.host.finrank_E'

theorem jetNum_of_sizes {D : D7} {L : SizeData₂ D} (S : SizesAt L) {dF : ℕ}
    (hd : (dF : ℝ) ≤ D.R.f * D.R.r * (2 * (2 * L.sc.b) + 1)) : JetNum D dF (1 / 2500) := by
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have a1 := D.R.two_le_m
  have a2 := D.R.m_add_three_le_k
  have a3 : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have a4 : D.R.f ≤ D.R.k := D.R.f_le_k
  have a5 : D.R.k ≤ D.R.r ∧ D.R.m ≤ D.R.r ∧ 6 ≤ D.R.r := by unfold Ranks.r; omega
  have ht : (11 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 11 ≤ D.R.t)
  have hf : (D.R.f : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.f ≤ D.R.t)
  have hm : (D.R.m : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.m ≤ D.R.t)
  have hr : (D.R.r : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.r ≤ D.R.t)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 0 ≤ L.sc.L := Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd' : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : D.host.rdE ≤ szCond L := by
    unfold szCond
    have h0 : (0 : ℝ) ≤ D.host.QS := Nat.cast_nonneg _
    have : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.QS * ((D.host.q : ℝ) * D.host.d) :=
      mul_le_mul_of_nonneg_left hs h0
    nlinarith [mul_nonneg h0 (Real.sqrt_nonneg ((D.host.q : ℝ) * D.host.d))]
  have hc1 : (1 : ℝ) ≤ szCond L := h1.trans hc
  have ht1 : (1 : ℝ) ≤ D.R.t := by linarith
  have sC' : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b := le_trans sC hsb
  have hb : (D.R.t : ℝ) ^ 7 ≤ L.sc.b :=
    ((pow_le_pow_right₀ ht1 (by norm_num)).trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1))).trans sC'
  have hrd : D.host.rdE ^ 2 ≤ L.sc.b :=
    (((pow_le_pow_left₀ (by linarith) hc 2).trans (pow_le_pow_right₀ hc1 (by norm_num))).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1))).trans sC'
  have hR : rr0 D ≤ L.sc.b := by
    have hn1 : (1 : ℝ) ≤ Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
    have e : |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) = D.host.rdE ^ 2 := by
      unfold Formalism.BasicNotions.Host.rdE
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      push_cast
      ring
    unfold rr0
    rw [e]
    exact (div_le_self (by positivity) (by linarith)).trans hrd
  intro k
  have hg : L.sc.b ^ 8 ≤ (D.host.g k : ℝ) :=
    (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
  obtain ⟨c1, c2, c3⟩ := jet_real (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ht hf hm hr hb hd hR hg
  exact ⟨by exact_mod_cast c1, c2, c3⟩

section Cols

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem mult_add_mult_conj (D : Datum H) (τ : E →+* ℂ) :
    D.mult τ + D.mult (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) = D.p + D.q :=
  _root_.GlobalTheory.ConjugateMultiplicitySum.mult_add_mult_conj D τ

theorem two_mul_rank_le_nCol (Dw : Datum H) : 2 * (Dw.p + Dw.q) ≤ nCol Dw := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h := mult_add_mult_conj Dw τ
  have hle : ∀ σ, Dw.mult σ ≤ Fintype.card (Lt1 Dw) := fun σ => by
    have := Fintype.card_le_of_injective (fun i : Fin (Dw.mult σ) => (⟨σ, i⟩ : Lt1 Dw))
      (@sigma_mk_injective _ (fun τ => Fin (Dw.mult τ)) σ)
    rwa [Fintype.card_fin] at this
  have h1 := hle τ
  have h2 := hle (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ)
  unfold nCol
  omega

end Cols

theorem log_g_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hL : 1 ≤ L.sc.L) (hf : 1 ≤ D.R.f) (hr : 1 ≤ D.R.r) :
    Real.log (D.host.g 0) + Real.log (D.host.g 1) ≤ (2 + 2 * P.CYL) * zBase L ^ 12 := by
  obtain ⟨Y, h1, -, h3, h4⟩ := P.g_Y
  have hk : (0 : ℝ) < D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : 0 < D.R.k)
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) h1
  have hg : ∀ i, Real.log (D.host.g i) ≤ L.sc.L + P.CYL * L.sc.L := fun i => by
    have a := Real.log_le_log (hY.trans_le (h4 i).1) (h4 i).2
    rw [Real.log_mul two_ne_zero hY.ne'] at a
    have := Real.log_two_lt_d9
    linarith
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hZ : L.sc.L ≤ zBase L := le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hf' hr')
  have hZ' : L.sc.L ≤ zBase L ^ 12 := hZ.trans (le_self_pow₀ (hL.trans hZ) (by norm_num))
  have := mul_le_mul_of_nonneg_left hZ' (show 0 ≤ 2 + 2 * P.CYL by linarith [P.CYL_pos])
  linarith [hg 0, hg 1]

theorem numbers_at_point : Size → Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → JetNum (Fm.D x ι) (DF (dat p i) (aOf p i u1)) (1 / 2500) ∧ 2 * (Fm.D x ι).R.r ≤ nCol (dat p i) ∧ (lenT p i PP : ℝ) * (Real.log ((Fm.D x ι).host.g 0) + Real.log ((Fm.D x ι).host.g 1)) ≤ C * unitE p := by
  intro hS
  refine Closed.imp (Closed.and (GlobalTheory.T.quotient_weight_gap_bounds hS) (GlobalTheory.T.length_unit_size_bounds hS)) ?_
  rintro eps Fm CH - ⟨⟨_, _, hA⟩, ⟨_, _, hB⟩⟩
  obtain ⟨x0, h⟩ := EvTied.and hA hB
  refine ⟨max 0 (2 + 2 * Fm.CYL), le_max_left _ _, x0, fun x hx hle ι p hp i hi u1 hu => ?_⟩
  obtain ⟨hA, hB⟩ := h x hx hle ι p hp
  obtain ⟨a1, -, a3, a4, a5, a6, -⟩ := hA i hi u1 hu
  obtain ⟨b1, b2, -, -, b5, b6⟩ := hB i
  refine ⟨jetNum_of_sizes (Fm.sizes x hx ι) ?_, a3 ▸ two_mul_rank_le_nCol _, ?_⟩
  · have hev : Even (nCol (dat p i)) := even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) eight_dvd_nCol)
    have := (GlobalTheory.T.thetaExponents_dominant_lastEntry_one_degree _ _ (dat p i) u1 (nCol (dat p i)) _ a1 hev a4 a5 a6).2.2.2.2
    rw [finrank_host, a3, Nat.mul_div_cancel_left _ two_pos] at this
    exact this
  · have hg := log_g_le (Fm.params x hx ι) b2 b5 b6
    rw [Fm.params_CYL x hx ι] at hg
    have hZ : 0 ≤ zBase (Fm.L x ι) ^ 12 := by positivity
    have hT : (0 : ℝ) ≤ lenT p i (Fm.parT x hx ι).PP := Nat.cast_nonneg _
    have hg' := hg.trans (mul_le_mul_of_nonneg_right (le_max_right 0 _) hZ)
    have h1 := mul_le_mul_of_nonneg_left hg' hT
    have h2 := mul_le_mul_of_nonneg_left b1 (le_max_left 0 (2 + 2 * Fm.CYL))
    linarith [mul_left_comm (lenT p i (Fm.parT x hx ι).PP : ℝ) (max 0 (2 + 2 * Fm.CYL)) (zBase (Fm.L x ι) ^ 12)]

end GlobalTheory.RefSum.NumPt
end

