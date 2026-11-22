import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0245
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0080
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0242
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0165
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FnFactor
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Fac

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

private theorem eq_of_sp_complex_pts (y y' : ↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) : y = y' := by
  have e : ∀ p : PrimeSpectrum ℂ, p.asIdeal = ⊥ := fun p => Ideal.eq_bot_of_prime p.asIdeal
  exact PrimeSpectrum.ext (R := ℂ) ((e y).trans (e y').symm)

theorem fn_factor (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ)
    (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ) (hθ : a.IsFn s θ)
    (l : a.u.Λ) (w : Fin g → ℂ) :
    θ (w + l) = (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) ^ n * θ w := by
  obtain ⟨-, -, -, hfr⟩ := a.ah
  obtain ⟨x0⟩ : Nonempty ↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) :=
    ⟨(IsLocalRing.closedPoint ℂ : PrimeSpectrum ℂ)⟩
  obtain ⟨i, hi⟩ : ∃ i : P.L.ι, ⊤ ≤ (TopologicalSpace.Opens.map (a.pt w).base).obj (P.L.U i) := by
    have hx : (a.pt w).base x0 ∈ (⨆ j, P.L.U j) := by
      rw [P.isLB.cover]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨j, fun y _ => ?_⟩
    rw [eq_of_sp_complex_pts y x0]
    exact hj
  have hz : ∀ v : Fin g → ℂ, ⊤ ≤ (TopologicalSpace.Opens.map (a.pt v).base).obj (P.L.U i) →
      ⊤ ≤ (TopologicalSpace.Opens.map (CategoryTheory.Over.Hom.left (a.u.ex v)).base).obj
        ((P.L.pull a.φ).U fun _ => i) := by
    intro v hv y hy
    exact Set.mem_iInter.2 fun _ => hv hy
  have hpt : a.pt (w + (l : Fin g → ℂ)) = a.pt w := by
    have h1 : a.u.ex (l : Fin g → ℂ) = 1 := (a.u.ker _).2 l.2
    change CategoryTheory.CategoryStruct.comp (CategoryTheory.Over.Hom.left (a.u.ex (w + (l : Fin g → ℂ)))) a.φ =
      CategoryTheory.CategoryStruct.comp (CategoryTheory.Over.Hom.left (a.u.ex w)) a.φ
    rw [a.u.ex_add, h1, _root_.mul_one]
  have hi' : ⊤ ≤ (TopologicalSpace.Opens.map (a.pt (w + (l : Fin g → ℂ))).base).obj (P.L.U i) := by
    rw [hpt]
    exact hi
  have hA := hθ i w hi
  have hB := hθ i (w + (l : Fin g → ℂ)) hi'
  rw [hpt] at hB
  have hE := hB.symm.trans hA
  have hF := a.u.fr_ne (fun _ => i) (w + (l : Fin g → ℂ)) (hz _ hi')
  have hw : a.u.fr (fun _ => i) w =
      (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) *
        a.u.fr (fun _ => i) (w + (l : Fin g → ℂ)) := hfr l (fun _ => i) w (hz w hi)
  rw [hw, mul_pow] at hE
  apply mul_right_cancel₀ (pow_ne_zero n hF)
  rw [hE]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.Fac
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoordinatesUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameVec

open GlobalTheory.CompanionTheory.Ar.LieSigma

theorem one_left_over {S : Scheme.{0}} {X M : Over S} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem isVec_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ), (∀ v, IsTangent v → ∃! w, a.u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ a.u.IsDiff w v) → ∀ x : D.B.carrier, ∃! c, D.IsVec a x c := by
  intro E _ _ _ H L _ _ D σ a h1 h2 x
  have hpull := isTanAt_pull D.t.G (σ.comp (algebraMap (𝓞 L) L)) (𝟙 _) (D.MB.pt x) (D.MB.tan x)
  have hw : (spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) ≫ D.t.G.hom
      = (epsAt (emb σ)).hom := by
    have := Over.w (pullEps (σ.comp (algebraMap (𝓞 L) L)) (𝟙 _) ≫ D.MB.pt x)
    simpa [pullEps] using this
  let v : epsAt (emb σ) ⟶ D.t.G := Over.homMk _ hw
  have hvl : v.left = spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left := rfl
  have hlift : D.MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 D.t.G.left) x v := by
    show v.left ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact hvl
  have hsq : v.left ≫ D.t.G.hom = (epsR ℂ).hom ≫ emb σ := hw
  let v' : epsR ℂ ⟶ a.A := Over.homMk (a.cart.1.lift v.left (epsR ℂ).hom hsq) (a.cart.1.lift_snd _ _ _)
  have hφ : v'.left ≫ a.φ = v.left := a.cart.1.lift_fst _ _ _
  have ht : IsTangent v' := by
    unfold IsTangent
    apply a.cart.1.hom_ext
    · have h3 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = _ := hpull
      rw [Category.assoc, hφ, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left a.cart, h3, one_left_over]
      simp
    · have e : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (epsR ℂ).hom = 𝟙 _ := by
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
          ext t <;> simp
        rw [this]
        exact Spec.map_id _
      rw [Category.assoc, Over.w v', e]
      simpa using (Over.w η[a.A]).symm
  obtain ⟨c, hc, hu⟩ := h1 v' ht
  refine ⟨c, ⟨v, hlift, v', hφ, hc⟩, ?_⟩
  rintro c' ⟨v₁, hl₁, v₁', hφ₁, hc₁⟩
  have e₁ : v₁.left = v.left := by
    have : v₁.left ≫ 𝟙 _ = _ := hl₁
    rw [Category.comp_id] at this
    exact this
  have e₂ : v₁' = v' := by
    apply Over.OverMorphism.ext
    apply a.cart.1.hom_ext
    · rw [hφ₁, hφ, e₁]
    · rw [Over.w v₁', Over.w v']
  exact hu c' (e₂ ▸ hc₁)

end GlobalTheory.CompanionTheory.Ar.Sl.FrameVec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_hodgeInnerProduct_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (M : LieModel t.G z V), (∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L) → ∃ h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, (∀ v w c, HodgeIP t.G t.PP.L z (M.pt v) (M.pt w) c ↔ c = h v w) ∧ (∀ v w, h w v = starRingEnd ℂ (h v w)) ∧ ∀ v, v ≠ 0 → 0 < (h v v).re := by
  intro E _ _ _ H X t z V _ _ M ⟨t', m, hP, hA⟩
  have hab : IsAbelianScheme t'.G := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ t'.G hab
  obtain ⟨u₀, hc⟩ := GlobalTheory.T.exists_exp_chart_coordinates t'.G t'.PP.L g hab hA hg
  obtain ⟨u, Hm, χ, hex, hH, hχ, hlaw⟩ := GlobalTheory.T.theta_multiplier_normal_form t'.G t'.PP t'.cub g u₀
  obtain ⟨N, J, Θ, hN, hd, hq, hne, hsep⟩ := GlobalTheory.T.exists_theta_basis_of_factor t'.G t'.PP.L g u Hm χ t'.PP.isLB hab hA hlaw
  have hpos := GlobalTheory.T.theta_functions_finite_dim g u.Λ u.discrete u.full Hm χ N J Θ hH hχ hN hd hq hne hsep
  have hAH : u.IsAH Hm χ := ⟨hH, hpos, hχ, hlaw⟩
  obtain ⟨ht₁, ht₂⟩ := @GlobalTheory.TangentOrigin.tangent_bijection_of_values @GlobalTheory.valAt'_rules t'.G _ t'.PP.L g u
    (by simpa only [hex] using hc)
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  have hL := t'.PP.isLB
  have hM := pull_isLB t.PP.isLB m.φ
  let u₁ : HolUnif t'.G (t.PP.L.pull m.φ) g := GlobalTheory.ArchMetricCompare.carry u hL hM hw₀
  have hAH₁ : u₁.IsAH Hm χ := GlobalTheory.ArchMetricCompare.carry_isAH hL hM hw₀ hAH
  have ht₁' : ∀ v, IsTangent v → ∃! w, u₁.IsDiff w v := ht₁
  have ht₂' : ∀ w, ∃! v, IsTangent v ∧ u₁.IsDiff w v := ht₂
  have hcart : IsGrpPullback t'.G t.G z m.φ := m.cart
  obtain ⟨D, hD⟩ := GlobalTheory.T.tangent_space_equiv_hol_unif X t.G z V M t'.G m.φ _ g u₁ hcart ht₁' ht₂'
  choose x hxt hxφ hxd using hD
  let h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun v w => (Real.pi : ℂ) * hermForm Hm (D w) (D v))
    (fun v v' w => by simp [hermForm, Matrix.mulVec_add, dotProduct_add, mul_add])
    (fun c v w => by
      simp [hermForm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]; ring)
    (fun v w w' => by simp [hermForm, add_dotProduct, mul_add])
    (fun c v w => by simp [hermForm, smul_dotProduct, smul_eq_mul]; ring)
  have hh : ∀ v w, h v w = (Real.pi : ℂ) * hermForm Hm (D w) (D v) := fun _ _ => rfl
  refine ⟨h, fun v w c => ⟨?_, ?_⟩, fun v w => ?_, fun v hv => ?_⟩
  · rintro ⟨-, -, -, A, _, φ, g', u', Hm', χ', v', w', a, b, h1, h2, h3, h4, h5, h6, rfl⟩
    have := GlobalTheory.T.hol_unif_compare_isogeny X t.G t.PP.L z t'.G A m.φ φ g g' u₁ u' Hm Hm' χ χ' t.PP.isLB hab hcart h1 ht₁' ht₂' hAH₁ h2
      (x w) (x v) w' v' (D w) (D v) b a (hxt w) (hxt v) (h4.trans (hxφ w).symm) (h3.trans (hxφ v).symm)
      (hxd w) (hxd v) h6 h5
    rw [hh, ← this]
    rfl
  · rintro rfl
    exact ⟨t.PP.isLB, M.tan v, M.tan w, t'.G, inferInstance, m.φ, g, u₁, Hm, χ, x v, x w, D v, D w, hcart, hAH₁,
      hxφ v, hxφ w, hxd v, hxd w, rfl⟩
  · rw [hh, hh, map_mul, Complex.conj_ofReal, GlobalTheory.CompanionTheory.Ar.conj_hermForm hH]
  · rw [hh, Complex.re_ofReal_mul]
    exact mul_pos Real.pi_pos (hpos _ (fun h0 => hv (D.map_eq_zero_iff.1 h0)))

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroCoordsOfNonzeroVector
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameZero

theorem tmul_one_injective {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ)
    (M : Type) [AddCommGroup M] [Module (𝓞 L) M] [Module.Projective (𝓞 L) M] (x : M)
    (h : (1 : ComplexAt σ) ⊗ₜ[𝓞 L] x = 0) : x = 0 := by
  have hinj : Function.Injective (Algebra.linearMap (𝓞 L) (ComplexAt σ)) := by
    intro a b hab
    have h1 : σ (a : L) = σ (b : L) := hab
    exact RingOfIntegers.coe_injective (σ.injective h1)
  have hr := Module.Flat.rTensor_preserves_injective_linearMap (M := M) _ hinj
  have h2 : (Algebra.linearMap (𝓞 L) (ComplexAt σ)).rTensor M ((1 : 𝓞 L) ⊗ₜ[𝓞 L] x) =
      (Algebra.linearMap (𝓞 L) (ComplexAt σ)).rTensor M 0 := by
    rw [LinearMap.rTensor_tmul, map_zero, Algebra.linearMap_apply, map_one, h]
  have h3 := hr h2
  have h4 := congrArg (TensorProduct.lid (𝓞 L) M) h3
  simpa using h4

theorem core_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (C : InnerProductSpace.Core ℂ V)
    (v : V) (h : (C.inner v v : ℂ).re = 0) : v = 0 := by
  apply C.definite
  have him : (C.inner v v : ℂ).im = 0 := by
    have h1 := C.conj_inner_symm v v
    have h2 := congrArg Complex.im h1
    simp only [Complex.conj_im] at h2
    linarith
  exact Complex.ext h him

theorem coord_ne_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type)
    [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x : D.B.carrier)
    (c : Fin D.g → ℂ) (hlen : D.len σ x ^ 2 = Real.pi * (a.herm c c).re) (hx : x ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hx
  have hherm : a.herm 0 0 = 0 := by simp [ArchFrame.herm]
  rw [hherm, Complex.zero_re, mul_zero] at hlen
  have hl : D.len σ x = 0 := by simpa using hlen
  have hnn : 0 ≤ (((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x)
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ)).re :=
    (D.B.metric.form σ).re_inner_nonneg _
  have hle := Real.sqrt_eq_zero'.mp hl
  exact tmul_one_injective σ D.B.carrier x (core_eq_zero _ _ (le_antisymm hle hnn))

end GlobalTheory.CompanionTheory.Ar.Sl.FrameZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionDifferentiable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem isFn_differentiable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ), a.IsFn s θ → Differentiable ℂ θ := by
  intro S G _ _ P z g a n s θ hθ w₀
  have hm : a.pt w₀ (default : PrimeSpectrum ℂ) ∈ ⨆ i, P.L.U i := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  have hi : ⊤ ≤ a.pt w₀ ⁻¹ᵁ P.L.U i := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi'
  let W : G.left.Opens := LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i)
  let Q : a.A.left.Opens := (P.L.pull a.φ).U (fun _ => i)
  let C : Set (Fin g → ℂ) := {w | ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ Q}
  have hCpt : ∀ w, w ∈ C → ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i := fun w h y hy =>
    Set.mem_iInter.1 (h hy) PUnit.unit
  have hptC : ∀ w, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i → w ∈ C := fun w h y hy =>
    Set.mem_iInter.2 fun _ => h hy
  have hCV : ∀ w, w ∈ C → ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (a.φ ⁻¹ᵁ W) := fun w h y hy =>
    Set.mem_iInter.2 fun _ => hCpt w h hy
  have ho : IsOpen C := (a.u.hol Q 0).1
  have hv : DifferentiableOn ℂ (fun w => valAt' (a.u.ex w).left (a.φ ⁻¹ᵁ W) ((a.φ.app W).hom (s.f fun _ => i))) C :=
    (a.u.hol _ _).2.mono hCV
  have hfr : DifferentiableOn ℂ (fun w => a.u.fr (fun _ => i) w ^ n) C := (a.u.fr_hol _).pow n
  have hne : ∀ w ∈ C, a.u.fr (fun _ => i) w ^ n ≠ 0 := fun w hw => pow_ne_zero n (a.u.fr_ne _ w hw)
  have hq : DifferentiableOn ℂ θ C := by
    refine (hv.mul (hfr.inv hne)).congr fun w hw => ?_
    have e := hθ i w (hCpt w hw)
    have e' : valF (a.pt w) W (s.f fun _ => i) = valAt' (a.pt w) W (s.f fun _ => i) := rfl
    have e4 : valAt' (a.u.ex w).left (a.φ ⁻¹ᵁ W) ((a.φ.app W).hom (s.f fun _ => i)) = θ w * a.u.fr (fun _ => i) w ^ n :=
      (GlobalTheory.valAt'_comp (a.u.ex w).left a.φ W (s.f fun _ => i)).trans (e'.symm.trans e)
    exact (mul_inv_cancel_right₀ (hne w hw) (θ w)).symm.trans (congrArg (· * (a.u.fr (fun _ => i) w ^ n)⁻¹) e4.symm)
  exact (hq.differentiableAt (ho.mem_nhds (hptC w₀ hi)))

end GlobalTheory.CompanionTheory.Ar.Sl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

variable {X Y : Scheme.{0}}

theorem valF_eq_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valF x U f = valAt' x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valF, dif_pos h, valAt', dif_pos h, valAt]
  · rw [valF, dif_neg h, valAt', dif_neg h]

theorem top_le_wchart {K : Type} [Fintype K] (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (i : L.ι)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U i) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : K => φ) (fun _ => i) :=
  fun p hp => Set.mem_iInter.2 fun _ => by
    have := h hp
    simpa using this

theorem valAt'_g_const {K : Type} [Fintype K] [Unique K] (L : LB X) (φ : Y ⟶ X) (e : ℤ) (x : Sp ℂ ⟶ Y) (i i' : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))) :
    valAt' x _ ((LB.LinComb L (K := K) (fun _ => φ) (fun _ => e)).g (fun _ => i) (fun _ => i')).val =
      valAt' (x ≫ φ) (L.U i ⊓ L.U i') (L.g i i').val ^ e := by
  have hle : LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i') ≤
      φ ⁻¹ᵁ (L.U i ⊓ L.U i') :=
    le_inf (inf_le_left.trans (LB.wchart_le L _ _ default)) (inf_le_right.trans (LB.wchart_le L _ _ default))
  have key : ((LB.LinComb L (K := K) (fun _ => φ) (fun _ => e)).g (fun _ => i) (fun _ => i') :
      Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ) =
      (res hle (pullU φ _ (L.g i i'))) ^ e :=
    Fintype.prod_unique (M := Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ) _
  refine (congrArg (fun u : Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓
    LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ => valAt' x _ u.val) key).trans ?_
  refine (valAt'_units_zpow x h _ e).trans ?_
  congr 1
  exact (valAt'_map x _ _ h).trans (valAt'_comp x φ _ _)

end GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameFn
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}

theorem exists_chart_pt (a : ArchFrame P z g) (w : Fin g → ℂ) : ∃ i, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i := by
  have h : a.pt w (default : PrimeSpectrum ℂ) ∈ (⨆ i, P.L.U i : G.left.Opens) := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 h
  exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩

theorem top_le_frame (a : ArchFrame P z g) (w : Fin g → ℂ) (i : P.L.ι) (h : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) :
    ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (P.L.pull a.φ).U (fun _ => i) :=
  top_le_wchart (K := PUnit) P.L a.φ (a.u.ex w).left i h

theorem top_le_sec (a : ArchFrame P z g) (n : ℕ) (w : Fin g → ℂ) (i : P.L.ι) (h : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) :
    ⊤ ≤ a.pt w ⁻¹ᵁ (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => i) :=
  top_le_wchart (K := Fin 1) P.L (𝟙 G.left) (a.pt w) i (by simpa using h)

theorem fr_change (a : ArchFrame P z g) (w : Fin g → ℂ) (i j : P.L.ι) (hi : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i)
    (hj : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U j) :
    a.u.fr (fun _ => i) w = valAt' (a.pt w) (P.L.U i ⊓ P.L.U j) (P.L.g i j).val * a.u.fr (fun _ => j) w := by
  have h : ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ ((P.L.pull a.φ).U (fun _ => i) ⊓ (P.L.pull a.φ).U (fun _ => j)) :=
    (top_le_preimage_inf _ _ _).2 ⟨top_le_frame a w i hi, top_le_frame a w j hj⟩
  refine (a.u.fr_compat _ _ w h).trans ?_
  have := valAt'_g_const (K := PUnit) P.L a.φ 1 (a.u.ex w).left i j h
  rw [zpow_one] at this
  exact congrArg (· * a.u.fr (fun _ => j) w) this

theorem sec_change (a : ArchFrame P z g) {n : ℕ} (s : Out.H0 P.L n) (w : Fin g → ℂ) (i j : P.L.ι)
    (hi : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) (hj : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U j) :
    valF (a.pt w) _ (s.f fun _ => i) =
      valAt' (a.pt w) (P.L.U i ⊓ P.L.U j) (P.L.g i j).val ^ n * valF (a.pt w) _ (s.f fun _ => j) := by
  have h : ⊤ ≤ a.pt w ⁻¹ᵁ ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => i) ⊓
      (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => j)) :=
    (top_le_preimage_inf _ _ _).2 ⟨top_le_sec a n w i hi, top_le_sec a n w j hj⟩
  have e := congrArg (valAt' (a.pt w) _) (s.compat (fun _ => i) (fun _ => j))
  rw [valAt'_mul, valAt'_map _ _ _ h, valAt'_map _ _ _ h] at e
  have t := valAt'_g_const (K := Fin 1) P.L (𝟙 G.left) (n : ℤ) (a.pt w) i j h
  rw [Category.comp_id, zpow_natCast] at t
  rw [valF_eq_valAt', valF_eq_valAt', e, t]

theorem unique_fn (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) : ∃! θ, a.IsFn s θ := by
  choose c hc using exists_chart_pt a
  have hne : ∀ w i, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i → a.u.fr (fun _ => i) w ≠ 0 :=
    fun w i h => a.u.fr_ne _ w (top_le_frame a w i h)
  refine ⟨fun w => valF (a.pt w) _ (s.f fun _ => c w) / a.u.fr (fun _ => c w) w ^ n, ?_, ?_⟩
  · intro i w hi
    have h1 := fr_change a w i (c w) hi (hc w)
    have h2 := sec_change a s w i (c w) hi (hc w)
    have n1 := hne w (c w) (hc w)
    show _ = _ / _ * _
    rw [h2, h1, mul_pow]
    field_simp
  · intro θ hθ
    funext w
    have := hθ (c w) w (hc w)
    rw [this, mul_div_assoc, div_self (pow_ne_zero _ (hne w _ (hc w))), _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

theorem GlobalTheory.CompanionTheory.Ar.Sl.frame_fn_existsUnique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n), ∃! θ, a.IsFn s θ :=
  by
  intro S G _ _ P z g a n s
  exact GlobalTheory.CompanionTheory.Ar.Sl.FrameFn.unique_fn a n s
end
end

