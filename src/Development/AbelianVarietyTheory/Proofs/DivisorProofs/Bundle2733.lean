import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentFactor_uniformised_groups_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → IsLocalHom ρ → ∃ (D₁ D₁' : DegData R' (maximalIdeal R')) (F₁ : Factor D₁.toPre D₁'.toPre) (A₁' : PolAV (Sp (FractionRing R'))) (G₁' : Over (Sp R')) (_ : GrpObj G₁') (_ : IsCommMonObj G₁') (U₁' : Unif (maximalIdeal R') D₁' A₁' G₁') (oA₁ : A₁'.OAct F₁.O) (oG₁ : RingAct G₁' F₁.O) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (inc₁ : G₁ ⟶ G₁') (pr₁ : G₁' ⟶ G₁), Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsSemiAbelian G₁' ∧ U₁'.toUnifPre.OLinear F₁.O F₁.o oA₁ oG₁ ∧ IsSemiAbelian G₁ ∧ IsMonHom inc₁ ∧ IsMonHom pr₁ ∧ inc₁ ≫ pr₁ = 𝟙 G₁ ∧ pr₁ ≫ inc₁ = oG₁.act F₁.e ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso ((abelian₂ G₁' U₁'.LG.L).pull (lift (fst G₁ G₁ ≫ inc₁) (snd G₁ G₁ ≫ inc₁ ≫ oG₁.act F₁.f) : G2 G₁ ⟶ G2 G₁').left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  first | exact @GlobalTheory.FactorPull.factor_baseChange | exact GlobalTheory.FactorPull.factor_baseChange | (intros; apply GlobalTheory.FactorPull.factor_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelSectionsLinearRingOfIntegersStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imageModel_sections_linear_ringOfIntegers : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ∀ i : L.B.ι, (s x).f i = ∑ k, ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (L.B.U i) (β k) * (s (u k)).f i := by
  first | exact @GlobalTheory.ImageModel.sec_linear | exact GlobalTheory.ImageModel.sec_linear | (intros; apply GlobalTheory.ImageModel.sec_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailRest
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SecsDesc

theorem assemble (hE : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) (hN : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F) → ∃ Φ' : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ' F) F) (hT : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), (∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) ∧ ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  intro R _ _ _ hR D C
  obtain ⟨k₀, hk₀⟩ := hN R hR D C
  have hn : 1 < C.n := C.n_prime.one_lt
  have part1 : ∀ j ≥ k₀, ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j),
      ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F := by
    intro j hj
    obtain ⟨Φ, hΦ⟩ := hE R hR D C j
    exact hk₀ (C.n ^ j) (hj.trans (Nat.lt_pow_self hn).le) Φ hΦ
  refine ⟨⟨k₀, part1⟩, fun F₁ => ?_⟩
  have key : ∀ k, k = C.n ^ (k₀ * 2) → ∃ Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k,
      ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F := by
    rintro k rfl
    exact part1 _ (Nat.le_mul_of_pos_right _ (by norm_num))
  obtain ⟨Φ, hΦ⟩ := key ((C.n ^ k₀) ^ 2) (pow_mul _ _ _).symm
  exact hT R hR D C (C.n ^ k₀) (C.n_odd.pow) Φ hΦ F₁

end GlobalTheory.Mum.SecsDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellStabiliserOfLocalRingBigCellLemStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_bigCell_stabiliser_of_localRingBigCell_lemma : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ p * g ∈ GlobalTheory.DblVac.KD σ W v ∧ GlobalTheory.DblVac.BigCell W v (p * g) := by
  first | exact @GlobalTheory.InertBigCell.exists_bigCell | exact GlobalTheory.InertBigCell.exists_bigCell | (intros; apply GlobalTheory.InertBigCell.exists_bigCell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceIntegralUnitaryPointsFixVacuumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_integralUnitaryPoints_fix_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
    ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)),
      (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) →
      (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ω (g, h) s = s := by
  first | exact @GlobalTheory.InertBridge.fix_vac | exact GlobalTheory.InertBridge.fix_vac | (intros; apply GlobalTheory.InertBridge.fix_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem finsum_match {α β : Type*} (F : α → ℂ) (G : β → ℚ) (Φ : α → β) (P : α → Prop)
    (hF0 : ∀ a, ¬ P a → F a = 0) (hF : ∀ a, P a → F a = G (Φ a))
    (hinj : ∀ a a', P a → P a' → Φ a = Φ a' → a = a') (hsurj : ∀ b, G b ≠ 0 → ∃ a, P a ∧ Φ a = b) :
    ∑ᶠ a, F a = ((∑ᶠ b, G b : ℚ) : ℂ) := by
  have hcast : ((∑ᶠ b, G b : ℚ) : ℂ) = ∑ᶠ b, (G b : ℂ) := by
    by_cases hfin : (Function.support G).Finite
    · simpa using (Rat.castHom ℂ).toAddMonoidHom.map_finsum hfin
    · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support]
      · simp
      · have : Function.support (fun b => (G b : ℂ)) = Function.support G := by
          ext b; simp
        rwa [this]
  have hP : ∀ a, F a ≠ 0 → P a := fun a ha => by by_contra h; exact ha (hF0 a h)
  rw [hcast, ← finsum_mem_support F, ← finsum_mem_support (fun b => (G b : ℂ))]
  apply finsum_mem_eq_of_bijOn Φ
  · refine ⟨?_, ?_, ?_⟩
    · intro a ha
      simp only [Function.mem_support] at ha ⊢
      rwa [hF a (hP a ha)] at ha
    · intro a ha a' ha' h
      exact hinj a a' (hP a ha) (hP a' ha') h
    · intro b hb
      simp only [Function.mem_support, ne_eq, Rat.cast_eq_zero] at hb
      obtain ⟨a, ha, rfl⟩ := hsurj b hb
      refine ⟨a, ?_, rfl⟩
      simp only [Function.mem_support, hF a ha]
      exact_mod_cast hb
  · intro a ha
    exact hF a (hP a ha)

end GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem ul_mem_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w)
    (g : GLw n w) : g ∈ UL n w ↔ (g.val.map (cj w))ᵀ * g.val = 1 := by
  unfold UL
  rw [if_neg hw]
  change cT (cj w) g.val * 1 * g.val = 1 ↔ _
  rw [Matrix.mul_one]
  rfl

theorem kapOrb_unit_eq_kapSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Monic → Q₂.Monic → Q₁.natDegree + Q₂.natDegree = n → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → ∀ B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → B₁.P = Q₁.map e.symm.toRingHom → B₂.P = Q₂.map e.symm.toRingHom → kapOrb n w Q₁ Q₂ ((KL n w : Set (UL n w)).indicator 1) = (B₁.kapSum B₂ : ℂ) := by
  intro E _ _ _ hU w hw K e he hint hval hq n Q₁ Q₂ hm₁ hm₂ hdeg hsep hc₁ hc₂ B₁ B₂ hu₁ hu₂ hP₁ hP₂
  have hBP : (B₁.prod B₂).P = (Q₁ * Q₂).map e.symm.toRingHom := by
    rw [GlobalTheory.UnitLemma.Orbit.prod_P, hP₁, hP₂, Polynomial.map_mul]
  have hBsep : (B₁.prod B₂).P.Separable := by rw [hBP]; exact hsep.map
  have hBsep' : (B₁.P * B₂.P).Separable := by rw [← GlobalTheory.UnitLemma.Orbit.prod_P]; exact hBsep
  have hBu : (B₁.prod B₂).g * (B₁.prod B₂).σ (B₁.prod B₂).g = 1 := Prod.ext hu₁ hu₂
  have hdim : Module.finrank K.E (B₁.prod B₂).A = n := by
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E (B₁.prod B₂).g)]
    change (B₁.prod B₂).P.natDegree = n
    rw [hBP, natDegree_map_eq_of_injective e.symm.injective, hm₁.natDegree_mul hm₂, hdeg]
  set B := B₁.prod B₂ with hB
  have hcK : ∀ y, K.c (e.symm y) = e.symm (cj w y) := fun y => by
    apply e.injective
    rw [he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  let tr : GLw n w → Matrix (Fin n) (Fin n) K.E := fun γ => γ.val.map e.symm
  have trmul : ∀ a b : GLw n w, tr (a * b) = tr a * tr b := fun a b => by
    ext i j; simp [tr, Matrix.mul_apply, map_sum]
  have trinj : ∀ a b : GLw n w, tr a = tr b → a = b := fun a b h =>
    Units.ext (Matrix.map_injective e.symm.injective h)
  have trU : ∀ γ : UL n w, ((tr γ.1).map K.c)ᵀ * tr γ.1 = 1 := fun γ => by
    have h := (ul_mem_iff hw γ.1).1 γ.2
    have h2 : ((tr γ.1).map K.c)ᵀ = ((γ.1.val.map (cj w))ᵀ).map e.symm := by
      ext i j; simp [tr, hcK]
    rw [h2]
    calc _ = (((γ.1.val.map (cj w))ᵀ * γ.1.val).map e.symm) := by
            ext i j; simp [tr, Matrix.mul_apply, map_sum]
      _ = 1 := by rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have trcp : ∀ γ : GLw n w, (tr γ).charpoly = γ.val.charpoly.map e.symm.toRingHom := fun γ =>
    Matrix.charpoly_map γ.val e.symm.toRingHom
  have pull : ∀ u : Matrix (Fin n) (Fin n) K.E, (u.map K.c)ᵀ * u = 1 → ∃ g : UL n w, tr g.1 = u := by
    intro u hu
    have h1 : ((u.map e).map (cj w))ᵀ * u.map e = 1 := by
      have h2 : ((u.map e).map (cj w))ᵀ = ((u.map K.c)ᵀ).map e := by
        ext i j; simp [he]
      have h3 := congrArg (fun M => M.map e) hu
      simp only [Matrix.map_one _ (map_zero e) (map_one e)] at h3
      rw [h2, ← h3]
      ext i j; simp [Matrix.mul_apply, map_sum]
    let g : GLw n w := ⟨u.map e, ((u.map e).map (cj w))ᵀ, mul_eq_one_comm.1 h1, h1⟩
    refine ⟨⟨g, (ul_mem_iff hw g).2 h1⟩, ?_⟩
    ext i j; simp [tr, g]
  have hmod : ∀ γ : UL n w, γ.1.val.charpoly = Q₁ * Q₂ →
      ∃ (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), IsModel B (tr γ.1) x ψ :=
    fun γ h => GlobalTheory.T.exists_isModel_of_unitary_charpoly_eq K B n (tr γ.1) (trU γ) hBu hBsep (by rw [trcp, h, hBP])
  have clEq : Equivalence (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      have h1 : ((u⁻¹ : B.Aˣ) : B.A) * (u : B.A) = 1 := Units.inv_mul u
      have h2 : B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A) = 1 := by rw [← map_mul, h1, map_one]
      rw [hu]
      linear_combination (-(x.1 : B.A)) * B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A) * h1 + (-(x.1 : B.A)) * h2
    · rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
      refine ⟨u * v, ?_⟩
      rw [hv, hu, Units.val_mul, map_mul]; ring
  have twEq : Equivalence (fun x y : UL n w => ∃ g, y = g⁻¹ * x * (MonoidHom.id (UL n w)) g) := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  let Fv : {x : B.Aˣ // B.σ (x : B.A) = x} → ℚ := fun x => K.eta (B₁.gramDet (x.1 : B.A).1) * B.N (x.1 : B.A)
  have Fv_resp : ∀ a b : {x : B.Aˣ // B.σ (x : B.A) = x},
      (∃ u : B.Aˣ, (b.1 : B.A) = a.1 * (u * B.σ (u : B.A))) → Fv a = Fv b := by
    rintro a b ⟨u, hu⟩
    have e1 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K B (a.1 : B.A) u).1
    have e2 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K B₁ (a.1 : B.A).1 (Units.map (MonoidHom.fst B₁.A B₂.A) u)).2
    simp only [Fv, hu]
    exact (congrArg₂ (· * ·) e2 e1).symm
  have Fv_out : ∀ a, Fv (Quot.out (Quot.mk _ a : B.Cl)) = Fv a := fun a =>
    Fv_resp _ _ (clEq.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ a : B.Cl))))
  let P : TwCl (MonoidHom.id (UL n w)) → Prop := fun c => c.rep.1.val.charpoly = Q₁ * Q₂
  let Φ : TwCl (MonoidHom.id (UL n w)) → B.Cl := fun c =>
    if h : P c then Quot.mk _ ⟨(hmod c.rep h).choose, (hmod c.rep h).choose_spec.choose_spec.1⟩
    else Quot.mk _ ⟨1, by simp⟩
  unfold kapOrb clSum InvAlg.kapSum
  refine finsum_match _ _ Φ P ?_ ?_ ?_ ?_
  · intro c hc
    exact if_neg hc
  · intro c hc
    have hc' : c.rep ∈ {γ : UL n w | γ.1.val.charpoly = Q₁ * Q₂} := hc
    rw [if_pos hc']
    obtain ⟨ψ, hψ⟩ := (hmod c.rep hc).choose_spec
    have hΦ : Φ c = Quot.mk _ ⟨(hmod c.rep hc).choose, hψ.1⟩ := dif_pos hc
    rw [hΦ]
    change _ = ((Fv (Quot.out (Quot.mk _ _ : B.Cl)) : ℚ) : ℂ)
    rw [Fv_out]
    beta_reduce
    rw [GlobalTheory.T.hermitian_lattice_local_unitary_twist E hU w hw K e he hval n Q₁ B₁ B₂ hBsep' hP₁ c.rep.1 _ ψ hψ,
      GlobalTheory.T.inert_orbitalIntegral_unit_eq_lattice_count E hU w hw K e he hint n B hBsep c.rep _ ψ hψ]
    simp only [Fv]
    push_cast
    rfl
  · intro c c' hc hc' h
    obtain ⟨ψ, hψ⟩ := (hmod c.rep hc).choose_spec
    obtain ⟨ψ', hψ'⟩ := (hmod c'.rep hc').choose_spec
    have hΦ : Φ c = Quot.mk _ ⟨(hmod c.rep hc).choose, hψ.1⟩ := dif_pos hc
    have hΦ' : Φ c' = Quot.mk _ ⟨(hmod c'.rep hc').choose, hψ'.1⟩ := dif_pos hc'
    rw [hΦ, hΦ'] at h
    obtain ⟨v, hv⟩ := clEq.eqvGen_iff.1 (Quot.eqvGen_exact h)
    obtain ⟨u, hu, hγu⟩ := GlobalTheory.T.hermitianModels_conj_unitary_of_norm_class K B n _ _ _ _ v ψ ψ' hψ hψ' hv
    obtain ⟨g, rfl⟩ := pull u hu
    have hcomm : c.rep * g = g * c'.rep := by
      apply Subtype.ext
      apply trinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, trmul, trmul]
      exact hγu
    rw [← Quot.out_eq c, ← Quot.out_eq c']
    refine Quot.sound ⟨g, ?_⟩
    change c'.rep = g⁻¹ * c.rep * g
    rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro k hk
    set a := Quot.out k with ha
    have hk' : Fv a ≠ 0 := hk
    have hN : B.N (a.1 : B.A) ≠ 0 := (mul_ne_zero_iff.1 hk').2
    obtain ⟨γm, ψ, hψ⟩ := GlobalTheory.T.exists_hermitianModel_of_norm_ne_zero K B n a.1 hdim a.2 hN
    obtain ⟨hcpm, hunm⟩ := GlobalTheory.T.hermitianModel_charpoly_eq_and_unitary K B n γm a.1 ψ hψ
    obtain ⟨γ, hγ⟩ := pull γm (hunm hBu)
    have hcpγ : γ.1.val.charpoly = Q₁ * Q₂ := by
      apply Polynomial.map_injective e.symm.toRingHom e.symm.injective
      rw [← trcp, hγ, hcpm, hBP]
    let c : TwCl (MonoidHom.id (UL n w)) := Quot.mk _ γ
    obtain ⟨g, hg⟩ := twEq.eqvGen_iff.1
      (Quot.eqvGen_exact (Quot.out_eq c : Quot.mk _ (Quot.out c) = Quot.mk _ γ))
    simp only [MonoidHom.id_apply] at hg
    have hcr : c.rep = g * γ * g⁻¹ := by
      change Quot.out c = g * γ * g⁻¹
      rw [hg]; group
    have hPc : P c := by
      change c.rep.1.val.charpoly = Q₁ * Q₂
      rw [hcr]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.coe_units_inv]
      rw [← hcpγ]
      exact Matrix.charpoly_units_conj (g.1) γ.1.val
    refine ⟨c, hPc, ?_⟩
    obtain ⟨ψc, hψc⟩ := (hmod c.rep hPc).choose_spec
    have hΦ : Φ c = Quot.mk _ ⟨(hmod c.rep hPc).choose, hψc.1⟩ := dif_pos hPc
    rw [hΦ]
    have hgu : γ * g⁻¹ = g⁻¹ * c.rep := by rw [hcr]; group
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_norm_mul_of_hermitianModel_unitary_conj K B n γm (tr c.rep.1) (tr (g⁻¹).1) a.1 _ ψ ψc hψ hψc (trU g⁻¹)
      (by rw [← hγ, ← trmul, ← trmul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hgu]) hBsep
    rw [← Quot.out_eq k]
    exact (Quot.sound ⟨v, hv⟩).symm

end GlobalTheory.InertUnitOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertTwUnit

theorem cast_finsum_rat {ι : Type} (f : ι → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, (f i : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have h1 : (Function.support f).Infinite := h
    have h2 : (Function.support fun i => (f i : ℂ)).Infinite := by
      have e : (Function.support fun i => (f i : ℂ)) = Function.support f := by
        ext i; simp
      rw [e]; exact h1
    rw [finsum_of_infinite_support h1, finsum_of_infinite_support h2, Rat.cast_zero]

theorem twisted_unit_eq_stSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = Q.map e.symm.toRingHom ∧ stTw a w Q ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) = (B.stSum : ℂ) := by
  intro E _ _ _ hU w hw K e hc hr hv hq a Q hm hd hs hQ
  unfold stTw IsCsr at *
  unfold clSum
  have hQ' : C ((cj w) (Q.coeff 0)) * Q = (Q.map (cj w)).reverse := hQ.resolve_left hw
  have hcomm : e.symm.toRingHom.comp (cj w) = (K.c : K.E →+* K.E).comp e.symm.toRingHom := by
    ext y
    have h := congrArg e.symm (hc (e.symm y))
    simp only [RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] at h
    simp [h]
  have hrev : ∀ p : (w.adicCompletion E)[X],
      (p.reverse).map e.symm.toRingHom = (p.map e.symm.toRingHom).reverse := by
    intro p
    unfold Polynomial.reverse
    rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective, Polynomial.reflect_map]
  have hPr : C (K.c ((Q.map e.symm.toRingHom).coeff 0)) * Q.map e.symm.toRingHom =
      ((Q.map e.symm.toRingHom).map (K.c : K.E →+* K.E)).reverse := by
    have h1 := congrArg (Polynomial.map e.symm.toRingHom) hQ'
    have h0 : e.symm.toRingHom ((cj w) (Q.coeff 0)) = K.c ((Q.map e.symm.toRingHom).coeff 0) := by
      rw [Polynomial.coeff_map]
      exact RingHom.congr_fun hcomm (Q.coeff 0)
    rw [Polynomial.map_mul, Polynomial.map_C, h0] at h1
    rw [h1, hrev, Polynomial.map_map, hcomm, ← Polynomial.map_map]
  obtain ⟨B, hg, hP⟩ := GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly K (Q.map e.symm.toRingHom) (hm.map _) hPr
  have hsep : B.P.Separable := by
    rw [hP]
    exact hs.map
  refine ⟨B, hg, hP, ?_⟩
  have hε : (-1 : B.A) ^ (a - 1) = 1 ∨ (-1 : B.A) ^ (a - 1) = -1 := neg_one_pow_eq_or B.A (a - 1)
  obtain ⟨β₀, hβ₀, hX⟩ := GlobalTheory.T.exists_basePoint_twistedHerm_unimodular_eq_selfDual K B hg hsep _ hε
  obtain ⟨F, hF⟩ := GlobalTheory.T.twistedConjugacyClasses_equiv_unitsModNorms_nonsplit E hU w hw K e hc hr a Q hm hd hs B hg hP β₀ hβ₀
  have hterm : ∀ k : B.Cl, twOrb (thL a w) (GlobalTheory.LFun.KGL w a) (F k).1.rep
      ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) = ((B.N k.rep : ℚ) : ℂ) := by
    intro k
    obtain ⟨b, hb⟩ := hF k
    have hu : B.σ (((Quot.out k).1 : B.Aˣ) : B.A) = ((Quot.out k).1 : B.Aˣ) := (Quot.out k).2
    have hβ : B.σ ((β₀ * (Quot.out k).1 : B.Aˣ) : B.A) =
        (β₀ * (Quot.out k).1 : B.Aˣ) * ((-1) ^ (a - 1) * B.g) := by
      rw [Units.val_mul, map_mul, hβ₀, hu]
      ring
    have h := GlobalTheory.T.twistedOrbitalIntegral_unitGL_eq_hermitianLatticeCount E hU w hw K e hc hr a B hsep (β₀ * (Quot.out k).1) _ hε hβ b (F k).1.rep
      (fun i j => by rw [Units.val_mul]; exact hb i j)
    rw [h, Units.val_mul, hX _ hu]
    rfl
  simp only [Set.mem_ofPred_eq, Pi.one_apply, one_mul]
  simp only [← finsum_eq_if]
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_comp_equiv F]
  simp only [hterm]
  exact (cast_finsum_rat _).symm

end GlobalTheory.InertTwUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteMapInj

theorem injective_of_finite_of_ringKrullDim_le (A R : Type) [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] (b : A →+* R) :
    b.Finite → ringKrullDim A ≤ ringKrullDim R → Function.Injective b := by
  intro hfin hdim
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  set I := RingHom.ker b
  have hxI : x ∈ I := hx

  have hcomp : b.kerLift.comp (Ideal.Quotient.mk I) = b := by
    ext a; rfl
  have hfin' : b.kerLift.Finite := by
    rw [← hcomp] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  letI : Algebra (A ⧸ I) R := b.kerLift.toAlgebra
  haveI : Algebra.IsIntegral (A ⧸ I) R := ⟨hfin'.to_isIntegral⟩
  have h1 : ringKrullDim R ≤ ringKrullDim (A ⧸ I) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (A ⧸ I) R))
      fun P Q h => Ideal.IsIntegral.comap_lt_comap (I := P.asIdeal) (J := Q.asIdeal) h
  have h2 : ringKrullDim (A ⧸ I) + 1 ≤ ringKrullDim A :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (mem_nonZeroDivisors_of_ne_zero hx0) (Ideal.Quotient.eq_zero_iff_mem.mpr hxI)
  have h3 : ringKrullDim R + 1 ≤ ringKrullDim R :=
    ((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans hdim
  have htop : ringKrullDim R + 1 < ⊤ :=
    ((by gcongr : ringKrullDim R + 1 ≤ ringKrullDim (A ⧸ I) + 1).trans h2).trans_lt
      ringKrullDim_lt_top
  have hbot : ringKrullDim R ≠ ⊥ := fun h => by
    have := ringKrullDim_nonneg_of_nontrivial (R := R)
    rw [h] at this
    exact absurd this (by simp)
  generalize ringKrullDim R = d at h3 htop hbot
  induction d with
  | bot => exact hbot rfl
  | coe e =>
    induction e with
    | top =>
      exact absurd htop (by rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]; exact lt_irrefl _)
    | coe n =>
      have : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : ℕ) := by exact_mod_cast h3
      norm_cast at this
      omega

end GlobalTheory.FiniteMapInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelEmbeddingSecondStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_embedding_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U h : Fin (Dw.mult σ) → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W σ))) (bcV Y.t φ e) (fun k b => φ (U k b))) → IsUnit (pairDet h U) → ∀ (T : CDVR) (α : A →+* T.V) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∀ (w : Fin (Dw.mult σ) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (gm : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr), (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U i b)) (w i ≫ Y.m.φ)) → (letI := io.toAlgebra; ∀ i, IsCombAt y₀.1.x (y₀.1.u σ) (gm i) (w i ≫ ν.φ)) → ∃ u : T.Vˣ, algebraMap T.V T.Fr u = gm.det := by
  first | exact @GlobalTheory.FlatModel.DetUnit.det_isUnit | exact GlobalTheory.FlatModel.DetUnit.det_isUnit | (intros; apply GlobalTheory.FlatModel.DetUnit.det_isUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFromSpecResidueFieldCompOfIsClosedOfClosStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Over (Sp R)), LocallyOfFiniteType X.hom → ∀ x : X.left, X.hom x = closedPoint R → IsClosed ({x} : Set X.left) → IsFinite (X.left.fromSpecResidueField x ≫ X.hom) := by
  first | exact @GlobalTheory.isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint | exact GlobalTheory.isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint | (intros; apply GlobalTheory.isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint <;> assumption)
end

