import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodRatioAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDeRhamPeriodMapEquivariant
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PeriodLattice

theorem periods_unif : GlobalTheory.Published.PeriodComparison →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    ∃ P : E →+ HdR X.A, Submodule.span ℂ (Set.range P) = ⊤ ∧
      ∀ (a : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) a * w' j) = U.u.ex w' ≫ α) →
        ∀ x, push (dp0 ℂ) (𝟙 _) α (P x) = P (a * x) := by
  intro hPC E _ _ _ I _ φ L 𝔠 X U
  obtain ⟨ε, hε⟩ := hPC
  obtain ⟨P₀, hspan, -, -, hend, -⟩ :=
    hε X.A (Module.finrank ℚ (FR E)) X.ab X.dim (X.diag U.c) (LB.isLB_pull (X.isLB _) _) U.u
  let em : E →ₗ[ℚ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun x j => φ (U.e j) x
      map_add' := fun x x' => by funext j; simp
      map_smul' := fun q x => by funext j; simp [Rat.smul_def] }
  have hem : ∀ x j, em x j = φ (U.e j) x := fun _ _ => rfl
  have hdc : ∀ x, (fun j => GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord φ 0 x (U.e j)) = em x := fun x => by
    funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, hem]
  let S : AddSubgroup E :=
    { carrier := {x | em x ∈ U.u.Λ}
      add_mem' := fun {a b} ha hb => by
        show em (a + b) ∈ U.u.Λ
        rw [map_add]; exact add_mem ha hb
      zero_mem' := by
        show em 0 ∈ U.u.Λ
        rw [map_zero]; exact zero_mem _
      neg_mem' := fun {a} ha => by
        show em (-a) ∈ U.u.Λ
        rw [map_neg]; exact neg_mem ha }
  have hemL : ∀ x ∈ S, em x ∈ U.u.Λ := fun x hx => hx
  let Q : S →+ HdR X.A :=
    { toFun := fun x => P₀ ⟨em x, hemL x x.2⟩
      map_zero' := by
        rw [show (⟨em ((0 : S) : E), hemL _ (0 : S).2⟩ : U.u.Λ) = 0 from
          Subtype.ext (by simp), map_zero]
      map_add' := fun x x' => by
        rw [← map_add]
        congr 1
        ext
        simp }
  have hsur : ∀ w ∈ U.u.Λ, ∃ x, em x = w := fun w hw => by
    obtain ⟨x, -, rfl⟩ := (U.lat w).1 hw
    exact ⟨x, (hdc x).symm⟩
  have hΛ : (U.u.Λ : Set (Fin (Module.finrank ℚ (FR E)) → ℂ)) = em '' (S : Set E) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, rfl⟩ := hsur w hw
      exact ⟨x, hw, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hemL x hx
  have hdim : Module.finrank ℚ E ≤ 2 * Module.finrank ℚ (FR E) := by
    rw [← Module.finrank_mul_finrank ℚ (FR E) E, Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E, mul_comm]
  have full : ∀ x : E, ∃ n : ℕ, 0 < n ∧ n • x ∈ S :=
    exists_nsmul_mem S em hdim (hΛ ▸ U.u.full)
  obtain ⟨P, hP⟩ := exists_ext S full Q
  have hP1 : ∀ x (hx : x ∈ S), P x = P₀ ⟨em x, hemL x hx⟩ := fun x hx => by
    rw [hP x 1 one_pos (by rw [one_smul]; exact hx), Nat.cast_one, inv_one, one_smul]
    show P₀ _ = P₀ _
    congr 2
    simp
  refine ⟨P, ?_, ?_⟩
  · refine top_unique (hspan ▸ Submodule.span_mono ?_)
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    obtain ⟨x, rfl⟩ := hsur w hw
    exact ⟨x, hP1 x hw⟩
  · intro a α _ hα x
    obtain ⟨n, hn, hnx⟩ := full x
    obtain ⟨m, hm, hmx⟩ := full (a * x)
    have hpos : 0 < n * m := Nat.mul_pos hn hm
    have hNx : (n * m) • x ∈ S := by
      rw [mul_comm, mul_smul]; exact S.nsmul_mem hnx _
    have hNax : (n * m) • (a * x) ∈ S := by
      rw [mul_smul]; exact S.nsmul_mem hmx _
    let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      { toFun := fun w j => φ (U.e j) a * w j
        map_add' := fun w w' => by funext j; simp [mul_add]
        map_smul' := fun r w => by funext j; simp; ring }
    rw [hP x _ hpos hNx, hP (a * x) _ hpos hNax, map_smul]
    congr 1
    exact hend α M (fun w => hα w) ⟨em ((n * m) • x), hemL _ hNx⟩ ⟨em ((n * m) • (a * x)), hemL _ hNax⟩
      (by funext j; simp only [hem, M, LinearMap.coe_mk, AddHom.coe_mk, map_nsmul, nsmul_eq_mul, map_mul]; ring)

end GlobalTheory.PeriodLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmOrderActionDescends
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem exists_lie_end_diagonal_of_tensor : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X) (p : X.A.left ⟶ X₀.A.left)
    (c : Ideal (OF E)) (cm : OAct (orderC c) X₀.A),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ cd : X₀.Lie →ₗ[R] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ v, ∃ v' : X.Lie, Obj.LieCorr R.subtype p v v' ∧ U.u.IsDiff (cd v) v'.hom) →
      (∀ v (v' : X.Lie) W, Obj.LieCorr R.subtype p v v' → U.u.IsDiff W v'.hom → W = cd v) →
    ∀ t : orderC c ⊗[ℤ] R, ∃ T : X₀.Lie →ₗ[R] X₀.Lie, ∀ v j, cd (T v) j =
      Algebra.TensorProduct.productMap ((φ (U.e j)).comp (orderC c).subtype).toIntAlgHom
        (algebraMap R ℂ).toIntAlgHom t * cd v j := by
  intro E _ _ I _ 𝔠 φ L R X₀ X U p c cm hcm cd hcd1 hcd2 t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, fun v j ↦ by simp⟩
  | add s t hs ht =>
    obtain ⟨S, hS⟩ := hs
    obtain ⟨T, hT⟩ := ht
    exact ⟨S + T, fun v j ↦ by
      rw [LinearMap.add_apply, map_add, Pi.add_apply, hS, hT, map_add, add_mul]⟩
  | tmul a x =>
    have := cm.hom a
    obtain ⟨α, hα, hp, hex⟩ := hcm a
    refine ⟨x • GlobalTheory.Serre.Lie.map X₀.rm X₀.rm (cm.act a), fun v j ↦ ?_⟩
    obtain ⟨v', hc, hd⟩ := hcd1 v
    let F : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
      LinearMap.pi fun j ↦ φ (U.e j) (a : E) • LinearMap.proj j
    have hd' := GlobalTheory.HomLinear.isDiff_comp U.u U.u α F (fun w ↦ hex w) v'.isTangent hd
    have hc' : Obj.LieCorr R.subtype p (GlobalTheory.Serre.Lie.map X₀.rm X₀.rm (cm.act a) v)
        (GlobalTheory.Serre.Lie.map X.rm X.rm α v') := by
      unfold Obj.LieCorr at hc ⊢
      rw [GlobalTheory.Serre.Lie.hom_map, GlobalTheory.Serre.Lie.hom_map, Over.comp_left, Over.comp_left,
        Category.assoc, hp, ← Category.assoc, hc, Category.assoc]
    have h := congrFun (hcd2 _ _ _ hc' hd') j
    rw [LinearMap.smul_apply, map_smul, Pi.smul_apply, ← h,
      Algebra.TensorProduct.productMap_apply_tmul]
    change (x : ℂ) * (φ (U.e j) (a : E) * cd v j) = φ (U.e j) (a : E) * (x : ℂ) * cd v j
    ring

end GlobalTheory.LatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodRatioAlgebraicStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_period_ratio_algebraic : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf io 1 Λ₀ → Ω₀ ^ 12 = latDisc Λ₀ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X) (X₀ : Obj (FR E) 𝔠 (Sp Qb))
        (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
      ∃ (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
        ∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧
          a i ≠ 0 ∧ IsAlgebraic ℚ (a i * Ω₀) := by
  first | exact @GlobalTheory.CMLiePeriod.exists_lie_frame | exact GlobalTheory.CMLiePeriod.exists_lie_frame | (intros; apply GlobalTheory.CMLiePeriod.exists_lie_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmSkewIdealFractionalIdealStatement
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_skew_ideal_fractional_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E) (ξ : E), ξ ≠ 0 → bar ξ = -ξ →
    (∀ m ∈ M, bar m = -m) → IsUnit M → ∃ 𝔠 : FracId (FR E), ∀ a : FR E, a ∈ 𝔠.elt ↔ (a : E) * ξ ∈ M := by
  first | exact @GlobalTheory.AntiInvFrac.fracId_of_antiInv | exact GlobalTheory.AntiInvFrac.fracId_of_antiInv | (intros; apply GlobalTheory.AntiInvFrac.fracId_of_antiInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceFormImaginaryPartStatement
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_trace_form_imaginary_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (t₁ : E) (ρ : ℝ), (∀ i, φ i t₁ = -Complex.I * ((ρ / 2 : ℝ) : ℂ)) →
    ∀ (a : FR E) (x y : E), ((Algebra.trace ℚ E ((a : E) * t₁ * x * bar y) : ℚ) : ℝ) =
      (∑ j, (φ (e j) (a : E) * (ρ : ℂ)) * φ (e j) x * starRingEnd ℂ (φ (e j) y)).im := by
  first | exact @GlobalTheory.trace_riemannForm_eq_im | exact GlobalTheory.trace_riemannForm_eq_im | (intros; apply GlobalTheory.trace_riemannForm_eq_im <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeConjugateInField
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory.CMTypeThroughField

theorem comp_bar {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K] (j : K →+* ℂ)
    (ψ : E →+* K) : j.comp (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar ψ) = ComplexEmbedding.conjugate (j.comp ψ) := by
  ext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar, RingHom.coe_comp, Function.comp_apply]
  exact IsCMField.complexEmbedding_complexConj E (j.comp ψ) x

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K]
    (ψ : E →+* K) : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar ψ) = ψ := by
  ext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar]

theorem isCMTypeIn_bar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (K : Type) [Field K] (j : K →+* ℂ) (I : Type)
    (φ : I → E →+* ℂ) (φK : I → E →+* K), (∀ i, j.comp (φK i) = φ i) → IsCMType φ →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMTypeIn (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
  intro E _ _ _ K _ j I φ φK hφ hcm σ
  have hinj : Function.Injective (fun ψ : E →+* K => j.comp ψ) := by
    intro a b h
    ext x
    exact j.injective (DFunLike.congr_fun h x)
  have key : ∀ i, (σ = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i) ∨ σ = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) ↔
      (j.comp σ = φ i ∨ j.comp σ = ComplexEmbedding.conjugate (φ i)) := by
    intro i
    rw [bar_bar, or_comm]
    constructor
    · rintro (h | h)
      · exact Or.inl (by rw [h, hφ])
      · exact Or.inr (by rw [h, comp_bar, hφ])
    · rintro (h | h)
      · exact Or.inl (hinj (by simp only; rw [h, hφ]))
      · exact Or.inr (hinj (by simp only; rw [h, comp_bar, hφ]))
  obtain ⟨i, hi, hu⟩ := hcm (j.comp σ)
  exact ⟨i, (key i).2 hi, fun i' hi' => hu i' ((key i').1 hi')⟩

end GlobalTheory.CMTypeThroughField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeRealEmbeddingEquivStatement
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_real_embedding_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∃ (e : Fin (Module.finrank ℚ (FR E)) ≃ I) (e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)),
      ∀ j (x : FR E), ((e' j x : ℝ) : ℂ) = φ (e j) (x : E) := by
  first | exact @GlobalTheory.CMEquiv.cmType_equiv | exact GlobalTheory.CMEquiv.cmType_equiv | (intros; apply GlobalTheory.CMEquiv.cmType_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatesEmbeddingsStatement
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_separates_embeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i k, i ≠ k → ∃ a : 𝓞 (FR E), φ i ((a : FR E) : E) ≠ φ k ((a : FR E) : E) := by
  first | exact @GlobalTheory.CMSep.exists_int_ne | exact GlobalTheory.CMSep.exists_int_ne | (intros; apply GlobalTheory.CMSep.exists_int_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatingInteger
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMSep

theorem exists_int_sep_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i : I, ∃ b₀ : 𝓞 (FR E), ∀ j : I, φ j ((b₀ : FR E) : E) = φ i ((b₀ : FR E) : E) → j = i := by
  intro E _ _ _ I _ φ hφ i

  let L : I → FR E →ₗ[ℚ] ℂ := fun j => ((φ j).comp (algebraMap (FR E) E)).toRatAlgHom.toLinearMap
  have hL : ∀ j (x : FR E), L j x = φ j (x : E) := fun j x => rfl
  let p : {j : I // j ≠ i} → Subspace ℚ (FR E) := fun j => LinearMap.ker (L j.1 - L i)
  have hp : ∀ j, p j ≠ ⊤ := by
    intro j htop
    obtain ⟨a, ha⟩ := exists_int_ne E I φ hφ j.1 i j.2
    have : ((a : FR E)) ∈ p j := htop ▸ Submodule.mem_top
    simp only [p, LinearMap.mem_ker, LinearMap.sub_apply, hL, sub_eq_zero] at this
    exact ha this
  have hcov : ⋃ j, (p j : Set (FR E)) ≠ Set.univ := by
    intro h
    obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ h
    exact hp j hj
  obtain ⟨x, hx⟩ : ∃ x : FR E, ∀ j : {j : I // j ≠ i}, x ∉ p j := by
    by_contra hno
    push_neg at hno
    exact hcov (Set.eq_univ_of_forall fun x => by
      obtain ⟨j, hj⟩ := hno x
      exact Set.mem_iUnion.mpr ⟨j, hj⟩)
  obtain ⟨y, hy0, hyint'⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset (FR E))
  have hyint := hyint' x (Finset.mem_singleton_self x)
  refine ⟨⟨y • x, hyint⟩, fun j hj => ?_⟩
  by_contra hji
  apply hx ⟨j, hji⟩
  simp only [p, LinearMap.mem_ker, LinearMap.sub_apply, hL, sub_eq_zero]
  have e : ((y • x : FR E) : E) = (y : E) * (x : E) := by simp [zsmul_eq_mul]
  change φ j ((y • x : FR E) : E) = φ i ((y • x : FR E) : E) at hj
  rw [e, map_mul, map_mul, map_intCast, map_intCast] at hj
  exact mul_left_cancel₀ (by exact_mod_cast hy0) hj

end GlobalTheory.CMSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneDiagSumEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem cobOne_diagSum_eq (p : ℕ) (R : Type) [CommRing R] (G : PDivGroup p R) (n m : ℕ) (hm : (m : R) = 0) :
    ∀ c ∈ symCocycles R (G.A n), cobOne R (G.A n) (diagSum R (G.A n) m c) = pullbackTwo (mulBy R (G.A n) m) c -
      (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n))
        (fun _ _ ↦ Commute.all _ _) c) • (1 : G.A n ⊗[R] G.A n) := by
  intro c hc
  have hd : diagSum R (G.A n) m c = ∑ i ∈ Finset.range m, multDiag R (G.A n) i c := by
    simp [diagSum, LinearMap.sum_apply]
  have hz : m • c = 0 := by rw [← Nat.cast_smul_eq_nsmul R, hm, zero_smul]
  rw [pullTwo_mulBy_eq c hc m, hz, add_zero, hd, Algebra.algebraMap_eq_smul_one]
  abel

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjectiveStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_cohomologous_of_de_rham_surjective : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), Function.Surjective (toH1O (X.hom ≫ 𝟙 _)) → ∀ u : Fn1 X, IsCoc (whole X) u → ∃ f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)), Cohom (whole X) u (fv f) := by
  first | exact @GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective | exact GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective | (intros; apply GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleIsCoboundary
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmitsurCohomologyH1

noncomputable def d0 (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D'] :
    D' →ₗ[D] D' ⊗[D] D' :=
  TensorProduct.mk D D' D' 1 - (TensorProduct.mk D D' D').flip 1

theorem amitsur_d0_apply (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D'] (a : D') :
    d0 D D' a = (1 : D') ⊗ₜ[D] a - a ⊗ₜ[D] (1 : D') := by
  simp [d0]

theorem cocycle_is_coboundary : ∀ (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D']
    [Module.FaithfullyFlat D D'] (c : D' ⊗[D] D'),
    (∀ (E : Type) [CommRing E] [Algebra D E] (f₁ f₂ f₃ : D' →ₐ[D] E),
      Algebra.TensorProduct.lift f₁ f₃ (fun _ _ ↦ Commute.all _ _) c =
        Algebra.TensorProduct.lift f₁ f₂ (fun _ _ ↦ Commute.all _ _) c +
          Algebra.TensorProduct.lift f₂ f₃ (fun _ _ ↦ Commute.all _ _) c) →
    ∃ a : D', c = (1 : D') ⊗ₜ[D] a - a ⊗ₜ[D] (1 : D') := by
  intro D D' _ _ _ _ c hc
  let i1 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') := Algebra.TensorProduct.includeLeft
  let i2 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') :=
    (Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeLeft
  let i3 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') :=
    (Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeRight
  have h := hc (D' ⊗[D] (D' ⊗[D] D')) i1 i2 i3
  have k1 : ∀ x : D' ⊗[D] D',
      Algebra.TensorProduct.lift i1 i3 (fun _ _ ↦ Commute.all _ _) x -
        Algebra.TensorProduct.lift i1 i2 (fun _ _ ↦ Commute.all _ _) x =
        LinearMap.lTensor D' (d0 D D') x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      simp [i1, i2, i3, amitsur_d0_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, ← hx, ← hy]; abel
  have k2 : ∀ x : D' ⊗[D] D',
      Algebra.TensorProduct.lift i2 i3 (fun _ _ ↦ Commute.all _ _) x = (1 : D') ⊗ₜ[D] x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      simp [i2, i3, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      rw [map_add, hx, hy, TensorProduct.tmul_add]
  have key : (1 : D') ⊗ₜ[D] c = LinearMap.lTensor D' (d0 D D') c := by
    rw [← k1, ← k2, h]; abel
  let q := (LinearMap.range (d0 D D')).mkQ
  have hq : (1 : D') ⊗ₜ[D] q c = 0 := by
    have : (1 : D') ⊗ₜ[D] q c = LinearMap.lTensor D' q ((1 : D') ⊗ₜ[D] c) := by simp
    rw [this, key, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have hz : q ∘ₗ d0 D D' = 0 := by
      ext a; simp [q]
    rw [hz]; simp
  have hq0 : q c = 0 := (Module.FaithfullyFlat.one_tmul_eq_zero_iff D _ (A := D') _).1 hq
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hq0
  exact ⟨a, by rw [← ha, amitsur_d0_apply]⟩

end GlobalTheory.AmitsurCohomologyH1
end

