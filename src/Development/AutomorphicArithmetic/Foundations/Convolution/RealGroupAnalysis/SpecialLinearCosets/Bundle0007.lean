import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0006
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle0004
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.InfOrthWW
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem sb_mul_w {F : Type} [Field F] [NumberField F] {v : P F} {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) :
    (fun m : M2 v => a (m * !![0, -1; 1, 0])) ∈ SB (M2 v) := by
  have h1 : (!![0, -1; 1, 0] : M2 v) * !![0, 1; -1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h2 : (!![0, 1; -1, 0] : M2 v) * !![0, -1; 1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  let e : M2 v ≃ₜ M2 v :=
    { toFun := fun m => m * !![0, -1; 1, 0]
      invFun := fun m => m * !![0, 1; -1, 0]
      left_inv := fun m => by simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      right_inv := fun m => by simp only [Matrix.mul_assoc, h2, Matrix.mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  obtain ⟨hl, hc⟩ := ha
  exact ⟨hl.comp_continuous e.continuous, hc.comp_homeomorph e⟩

private theorem infOrth_wW (F : Type) [Field F] [NumberField F] : InfOrth (wW F) := by
  intro i j
  have h : (wW F).1 * (wW F).1ᵀ = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [wW, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  rw [h]

theorem UpperTheory.ConvolutionTheory.R2.I.omW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (v : P F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) D.δ → θ ≠ 0 →
      (∀ u (a : M2 v → ℂ) (b : Kv v) (φ : S4 F), φ.1 = ten v θ u (Pt a) →
        (W.Om (nU (sg v b)) φ).1 = ten v θ u (Pt fun m => a (m * !![1, b; 0, 1]))) ∧
      ∀ u, GoodU v D.δ θ u → ∃ u', GoodU v D.δ θ u' ∧ ∀ a ∈ SB (M2 v), ∀ φ : S4 F, φ.1 = ten v θ u (Pt a) →
        (W.Om (wW F) φ).1 = ten v θ u' (Pt fun m => a (m * !![0, 1; -1, 0])) := by
  intro F E _ _ _ _ _ _ _ D W v θ hθ hne
  obtain ⟨-, -, hq, -⟩ := UpperTheory.ConvolutionTheory.R2.I.matLaws F v D.δ θ hθ hne
  obtain ⟨-, hψ, -⟩ := UpperTheory.ConvolutionTheory.R2.I.psiLaws F v
  obtain ⟨T, hT⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have hPt : ∀ a ∈ SB (M2 v), Pt a ∈ SB (M2 v) := fun a ha => by
    have := (T ⟨a, ha⟩).2
    rwa [hT] at this
  refine ⟨?_, ?_⟩
  · intro u a b φ hφ
    funext X
    rw [W.Om_n, hφ, hq, hψ]
    simp only [ten]
    rw [← ((UpperTheory.ConvolutionTheory.R2.I.ptN F v a (mat v θ X)).1 b)]
    ring
  · intro u hu
    obtain ⟨u', hu'⟩ := UpperTheory.ConvolutionTheory.R2.I.tenFt F v D.δ θ hθ hne u hu
    have key : ∀ a ∈ SB (M2 v), ∀ φ : S4 F, φ.1 = ten v θ u (Pt a) →
        (W.Om (wW F) φ).1 = ten v θ u' (Pt fun m => a (m * !![0, 1; -1, 0])) := by
      intro a ha φ hφ
      funext X
      rw [W.Om_w, hφ, hu' _ (hPt a ha)]
      simp only [ten]
      rw [UpperTheory.ConvolutionTheory.R2.I.ptW F v a ha]
    refine ⟨u', ?_, key⟩
    intro b hb
    obtain ⟨a1, ha1, rfl⟩ := ((UpperTheory.ConvolutionTheory.R2.I.ptInv F v b hb).2)
    have ha := sb_mul_w ha1
    obtain ⟨φ, hφF, hφ⟩ := hu _ (hPt _ ha)
    obtain ⟨U, hU, -, hk⟩ := (UpperTheory.ConvolutionTheory.R2.fockSt F E D W).om φ hφF {wW F} isCompact_singleton
      (by rintro k rfl; exact infOrth_wW F)
    refine ⟨W.Om (wW F) φ, hU (hk _ rfl), ?_⟩
    rw [key _ ha φ hφ]
    congr 2
    funext m
    have h2 : (!![0, 1; -1, 0] : M2 v) * !![0, -1; 1, 0] = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IsClosedEmbeddingSlVal
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem isClosedEmbedding_slVal {F : Type} [Field F] [NumberField F] (v : P F) :
    IsClosedEmbedding (fun m : SL v => (m.1 : M2 v)) := by
  have hc : IsClosed {A : M2 v | A.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  exact hc.isClosedEmbedding_subtypeVal

private noncomputable def resL {F : Type} [Field F] [NumberField F] (v : P F) :
    SB (M2 v) →ₗ[ℂ] SB (SL v) where
  toFun b := ⟨fun m => b.1 m.1,
    b.2.1.comp_continuous (isClosedEmbedding_slVal v).continuous,
    b.2.2.comp_isClosedEmbedding (isClosedEmbedding_slVal v)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def trM {F : Type} [Field F] [NumberField F] {v : P F} (g : SL v)
    (b : SB (M2 v)) : SB (M2 v) :=
  let e : M2 v ≃ₜ M2 v :=
    { toFun := fun m => m * g.1
      invFun := fun m => m * (g⁻¹ : SL v).1
      left_inv := fun m => by
        show m * g.1 * (g⁻¹ : SL v).1 = m
        rw [mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, mul_one]
      right_inv := fun m => by
        show m * (g⁻¹ : SL v).1 * g.1 = m
        rw [mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  ⟨fun m => b.1 (e m), b.2.1.comp_continuous e.continuous, b.2.2.comp_homeomorph e⟩

theorem UpperTheory.ConvolutionTheory.R2.I.absM :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLv v) V), (∀ f, IsOpen {g | ρ g f = f}) →
      ∀ β : V →ₗ[ℂ] SB (M2 v) →ₗ[ℂ] ℂ,
      (∀ (g : SL v) f (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m * g.1)) → β (ρ (Matrix.SpecialLinearGroup.toGL g) f) a' = β f a) →
      (∀ f (s : Kv v) (a a' : SB (M2 v)), (∀ m, a'.1 m = ψl v (-(s * m.det)) * a.1 m) → β f a' = ψl v (-s) * β f a) →
      ∀ f (a : SB (M2 v)) (aa : GLv v → SB (M2 v)),
        (∀ x m, (aa x).1 m = a.1 ((x⁻¹).val * m * (dd x).val)) → (fun x => β (ρ (dd x) f) (aa x)) ∈ MC ρ := by
  intro F _ _ v V _ _ ρ hρ β hinv hψ f a aa haa
  have hsurj : Function.Surjective (resL v) := by
    intro c
    obtain ⟨b, hb⟩ := UpperTheory.ConvolutionTheory.R2.I.ext F v c
    exact ⟨b, Subtype.ext (funext hb)⟩
  obtain ⟨s, hs⟩ := (resL v).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  have hs' : ∀ c, resL v (s c) = c := fun c => LinearMap.congr_fun hs c
  have hdep : ∀ (h : V) (b : SB (M2 v)), β h (s (resL v b)) = β h b := by
    intro h b
    have hz : β h (s (resL v b) - b) = 0 := by
      refine UpperTheory.ConvolutionTheory.R2.I.loc F v (β h) (fun t a a' ha => hψ h t a a' ha) _ ?_
      intro m hm
      have h1 : (s (resL v b)).1 m = b.1 m :=
        congrArg (fun c : SB (SL v) => c.1 ⟨m, hm⟩) (hs' (resL v b))
      show (s (resL v b)).1 m - b.1 m = 0
      rw [h1, sub_self]
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  have key := UpperTheory.ConvolutionTheory.R2.I.absS F v V ρ hρ (β.compl₂ s) ?_ f (resL v a)
    (fun x => resL v (aa x)) ?_
  · have hfun : (fun x => β (ρ (dd x) f) (aa x)) =
        fun x => (β.compl₂ s) (ρ (dd x) f) (resL v (aa x)) := by
      funext x
      rw [LinearMap.compl₂_apply, hdep]
    rw [hfun]
    exact key
  · intro g h c c' hc
    rw [LinearMap.compl₂_apply, LinearMap.compl₂_apply]
    have e : resL v (trM g (s c)) = c' := by
      apply Subtype.ext
      funext m
      have h1 : (s c).1 (m * g).1 = c.1 (m * g) :=
        congrArg (fun d : SB (SL v) => d.1 (m * g)) (hs' c)
      rw [hc m, ← h1]
      rfl
    rw [← e, hdep]
    exact hinv g h (s c) (trM g (s c)) (fun m => rfl)
  · intro x m m' hm
    show (aa x).1 m.1 = a.1 m'.1
    rw [haa, hm]
end

