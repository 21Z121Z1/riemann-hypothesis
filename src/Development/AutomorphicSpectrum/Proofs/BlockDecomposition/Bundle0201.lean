import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegrandTensor
section
noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RgEisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

theorem zetaIntegrand_tensor {k : Type} [Field k] [NumberField k]
    (φ : 𝓢(Unit → mixedSpace k, ℂ)) (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (ω : HeckeCharacter k) (s : ℂ) (x : IdeleGroup k) :
    GJMatrix.schwartzBruhatTensorPi φ g (fun _ => (x : 𝔸[k])) * (ω.toIdele x : ℂ) *
        ((ideleModule k x : ℝ) : ℂ) ^ s =
      (rd φ (fun _ => ((toInfinite k x : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k)) *
          (ω.toIdele (ofInfinite (toInfinite k x)) : ℂ) *
          ((ideleModule k (ofInfinite (toInfinite k x)) : ℝ) : ℂ) ^ s) *
        (g (fun _ => ((toFinite k x : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k)) *
          (ω.toIdele (ofFinite (toFinite k x)) : ℂ) *
          ((ideleModule k (ofFinite (toFinite k x)) : ℝ) : ℂ) ^ s) := by
  have hchi : (ω.toIdele x : ℂ) = (ω.toIdele (ofFinite (toFinite k x)) : ℂ) *
      (ω.toIdele (ofInfinite (toInfinite k x)) : ℂ) := by
    rw [← Circle.coe_mul, ← map_mul, ofFinite_mul_ofInfinite]
  have hmod : ((ideleModule k x : ℝ) : ℂ) ^ s =
      ((ideleModule k (ofInfinite (toInfinite k x)) : ℝ) : ℂ) ^ s *
        ((ideleModule k (ofFinite (toFinite k x)) : ℝ) : ℂ) ^ s := by
    have h : (ideleModule k x : ℝ) = (ideleModule k (ofInfinite (toInfinite k x)) : ℝ) *
        (ideleModule k (ofFinite (toFinite k x)) : ℝ) := by
      conv_lhs => rw [← ofFinite_mul_ofInfinite x, map_mul]
      rw [mul_comm]
      rfl
    rw [h, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (ideleModule k _).2.le
      (ideleModule k _).2.le]
  rw [hchi, hmod]
  change φ (fun _ => homeomorphMixedSpace k (x : 𝔸[k]).1) * g (fun _ => (x : 𝔸[k]).2) * _ * _ = _
  change _ = (φ (fun _ => homeomorphMixedSpace k (x : 𝔸[k]).1) * _ * _) *
    (g (fun _ => (x : 𝔸[k]).2) * _ * _)
  ring

theorem zSplit : ZSplit := by
  intro k _ _ φ g ω s _
  set A : (InfiniteAdeleRing k)ˣ → ℂ := fun a =>
    rd φ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) *
      ((ideleModule k (ofInfinite a) : ℝ) : ℂ) ^ s with hA
  set B : (FiniteAdeleRing (𝓞 k) k)ˣ → ℂ := fun b =>
    g (fun _ => (b : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite b) : ℂ) *
      ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ s with hB
  have hF : ∀ x : IdeleGroup k,
      GJMatrix.schwartzBruhatTensorPi φ g (fun _ => (x : 𝔸[k])) * (ω.toIdele x : ℂ) *
        ((ideleModule k x : ℝ) : ℂ) ^ s = (fun p => A p.1 * B p.2) (prodEquiv k x) :=
    zetaIntegrand_tensor φ g ω s
  have hemb : MeasurableEmbedding (prodEquiv k) :=
    (prodEquiv k).toHomeomorph.measurableEmbedding
  unfold globalZeta zInf zFin
  simp_rw [hF]
  rw [(measurePreserving_prodEquiv (K := k)).integral_comp hemb (fun p => A p.1 * B p.2)]
  exact integral_prod_mul A B

end GlobalTheory.CompanionTheory.RgEisTF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOne
section
noncomputable section

open NumberField Matrix MeasureTheory
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMG

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

variable {k : Type} [Field k] [NumberField k]

theorem lineZeta_ratV_unit (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ)
    (ξ : Unit → k) (hξ : ξ ≠ 0) : lineZeta Ψ₁ ω z (ratV ξ) = tate Ψ₁ ω z := by
  have h0 : ξ () ≠ 0 := fun h => hξ (funext fun i => by cases i; exact h)
  haveI := isHaarMeasure_ideleMeasure k
  haveI := IdeleGroup.borelSpace k
  have key := integral_mul_left_eq_self (μ := ideleMeasure k)
    (fun x : IdeleGroup k => Ψ₁ (fun _ => (x : 𝔸[k])) * ((ω.toIdele x : Circle) : ℂ) *
      ((((IdeleGroup.ideleModule k x : {r : ℝ // 0 < r}) : ℝ) : ℂ) ^ z))
    (IdeleGroup.diagonal k (Units.mk0 (ξ ()) h0))
  refine Eq.trans ?_ key
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : ((x : 𝔸[k]) • ratV ξ) =
      fun _ => ((IdeleGroup.diagonal k (Units.mk0 (ξ ()) h0) * x : IdeleGroup k) : 𝔸[k]) := by
    funext i
    cases i
    simp [ratV, IdeleGroup.diagonal, mul_comm]
  simp only [hx, map_mul, HeckeCharacter.toIdele_diagonal, IdeleGroup.ideleModule_diagonal, one_mul]

theorem proj_unit_eq (l l' : Projectivization k (Unit → k)) : l = l' := by
  induction l using Projectivization.ind
  rename_i v hv
  induction l' using Projectivization.ind
  rename_i w hw
  rw [Projectivization.mk_eq_mk_iff']
  have hw0 : w () ≠ 0 := fun h => hw (funext fun i => by cases i; exact h)
  exact ⟨v () / w (), funext fun i => by cases i; simp [div_mul_cancel₀ _ hw0]⟩

theorem epstein_unit_one (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ) :
    epstein Ψ₁ ω z 1 = tate Ψ₁ ω z := by
  have hne : (fun _ : Unit => (1 : k)) ≠ 0 := fun h => one_ne_zero (congrFun h ())
  unfold epstein
  rw [tsum_eq_single (Projectivization.mk k (fun _ : Unit => (1 : k)) hne)
    (fun b hb => absurd (proj_unit_eq b _) hb)]
  simp only [inv_one, Units.val_one, Matrix.one_mulVec]
  exact lineZeta_ratV_unit Ψ₁ ω z _ (Projectivization.rep_nonzero _)

theorem zetaOne_of_epMain : EpMain → ZetaOne := by
  intro h
  unfold EpMain at h
  unfold ZetaOne
  intro k _ _ Ψ₁ ω hΨ hω
  obtain ⟨V, -, hV⟩ := h k
  obtain ⟨F, F', hF, -, -, -⟩ := hV Unit Ψ₁ ω hΨ hω
  refine ⟨fun z => F z 1, ?_, fun z hz => ?_⟩
  · unfold PolyEnt
    refine ⟨hF.entire 1, fun b c => ?_⟩
    obtain ⟨M, hM⟩ := hF.strip b c {1} isCompact_singleton
    exact ⟨M, fun z h1 h2 => hM z h1 h2 1 rfl⟩
  · show F z 1 = _
    rw [hF.eq z (by simpa using hz) 1, epstein_unit_one]
    simp

end GlobalTheory.CompanionTheory.EisMG
end
end

