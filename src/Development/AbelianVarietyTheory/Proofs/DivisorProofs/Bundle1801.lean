import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1767
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1768
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticExtensionSymplecticCoordinatesStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_extension_symplectic_coordinates : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (K : Matrix (Fin d) (Fin d) E), (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 →
    ∃ p q : (Fin d → AE F E) ≃ₗ[AF F] (Fin 2 × Fin d → AF F),
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l))) ∧
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (∑ j, ∑ l, a j * incM F K j l * cA σ (b l))) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, p (incV F a) = fun k => algebraMap F (AF F) (y k)) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, q (incV F a) = fun k => algebraMap F (AF F) (y k)) := by
  first | exact @GlobalTheory.PairCoords.exists_pair_coords | exact GlobalTheory.PairCoords.exists_pair_coords | (intros; apply GlobalTheory.PairCoords.exists_pair_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompare
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

theorem sumElim_weylM_map {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]
    [Algebra F R] (a b a' b' : κ → R) :
    Sum.elim a b ⬝ᵥ ((weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R)) *ᵥ Sum.elim a' b' =
      a ⬝ᵥ b' - a' ⬝ᵥ b := by
  simp only [weylM, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec]
  simp [Matrix.map_neg, Matrix.neg_mulVec, dotProduct_comm b a', sub_eq_add_neg]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in

theorem darboux_change_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (c₁ c₂ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₁.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₂.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      GlobalTheory.SympChange.IsSymp G ∧ ∀ w, c₂.e w = GlobalTheory.SympChange.spAct G (c₁.e w) := by
  intro F E _ _ _ _ _ σ n d JX JW c₁ c₂ h₁ h₂
  classical
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have hAinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective _ _

  have honto : ∀ y z : Fin n × Fin d → F, ∃ x : Matrix (Fin n) (Fin d) E,
      c₁.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro y z
    let I : Matrix (Fin n) (Fin d) E →ₗ[F] Matrix (Fin n) (Fin d) (AE F E) :=
      (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
    let L : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      (c₁.e.toLinearMap.restrictScalars F).comp I
    have hL : ∀ x, L x = c₁.e (incM F x) := fun x => rfl
    let r : (Fin n × Fin d → F) →ₗ[F] (Fin n × Fin d → AF F) :=
      LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)
    let R : ((Fin n × Fin d → F) × (Fin n × Fin d → F)) →ₗ[F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      LinearMap.prodMap r r
    have hR : ∀ y z, R (y, z) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) :=
      fun _ _ => rfl
    have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
    have hRinj : Function.Injective R := fun a b h =>
      Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
    have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
      Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
    have hLinj : Function.Injective L := c₁.e.injective.comp hIinj
    have hle : LinearMap.range L ≤ LinearMap.range R := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y', z', h⟩ := h₁ x
      exact ⟨(y', z'), by rw [hR, hL, h]⟩
    have hdim : Fintype.card (Fin n) * Fintype.card (Fin d) * Module.finrank F E =
        Fintype.card (Fin n × Fin d) + Fintype.card (Fin n × Fin d) := by
      have h1 := c₁.e.finrank_eq
      rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h1
      exact h1
    have hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R) := by
      rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
        Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hdim]
    have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
    obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
    exact ⟨x, by rw [← hL, hx, hR]⟩

  let g : ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) ≃ₗ[AF F]
      ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) := c₁.e.symm.trans c₂.e
  have hgrat : ∀ y z : Fin n × Fin d → F, ∃ y' z' : Fin n × Fin d → F,
      g (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) =
        (fun i => algebraMap F (AF F) (y' i), fun i => algebraMap F (AF F) (z' i)) := by
    intro y z
    obtain ⟨x, hx⟩ := honto y z
    obtain ⟨y', z', h⟩ := h₂ x
    exact ⟨y', z', by rw [← hx]; simp only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, h]⟩
  let S := LinearEquiv.sumArrowLequivProdArrow (Fin n × Fin d) (Fin n × Fin d) (AF F) (AF F)
  let φ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) →ₗ[AF F] ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) :=
    (S.symm.toLinearMap.comp g.toLinearMap).comp S.toLinearMap
  have hφ : ∀ s, φ s = S.symm (g (S s)) := fun s => rfl
  have hent : ∀ i j, ∃ c : F, LinearMap.toMatrix' φ i j = algebraMap F (AF F) c := by
    intro i j
    rw [LinearMap.toMatrix'_apply]
    obtain ⟨y', z', h⟩ := hgrat (fun k => (Pi.single j (1 : F) : _ → F) (Sum.inl k))
      (fun k => (Pi.single j (1 : F) : _ → F) (Sum.inr k))
    have hS : S (Pi.single j 1) = (fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : _ → F) (Sum.inl k)),
        fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : _ → F) (Sum.inr k))) := by
      ext k <;> simp [S, Pi.single_apply, apply_ite]
    refine ⟨Sum.elim y' z' i, ?_⟩
    rw [hφ, hS, h]
    cases i <;> simp [S]
  obtain ⟨G, hG⟩ : ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      ∀ i j, LinearMap.toMatrix' φ i j = algebraMap F (AF F) (G i j) :=
    ⟨Matrix.of fun i j => (hent i j).choose, fun i j => (hent i j).choose_spec⟩
  have hGm : G.map (algebraMap F (AF F)) = LinearMap.toMatrix' φ := Matrix.ext fun i j => (hG i j).symm
  have hact : ∀ u, g u = spAct G u := by
    intro u
    have h1 : spAct G u = S (LinearMap.toMatrix' φ *ᵥ S.symm u) := by
      rw [← hGm]; rfl
    rw [h1, LinearMap.toMatrix'_mulVec, hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

  have hstd : ∀ u u' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F),
      S.symm u ⬝ᵥ (weylM.map (algebraMap F (AF F))) *ᵥ S.symm u' = u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 := by
    intro u u'
    obtain ⟨a, b⟩ := u
    obtain ⟨a', b'⟩ := u'
    have hs : ∀ p q : Fin n × Fin d → AF F, S.symm (p, q) = Sum.elim p q := fun p q => funext fun k => by
      cases k <;> simp [S]
    rw [hs, hs]
    exact sumElim_weylM_map a b a' b'
  have hkeep : ∀ u u' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F),
      (g u).1 ⬝ᵥ (g u').2 - (g u').1 ⬝ᵥ (g u).2 = u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 := by
    intro u u'
    have e2 := c₂.form (c₁.e.symm u) (c₁.e.symm u')
    have e1 := c₁.form (c₁.e.symm u) (c₁.e.symm u')
    simp only [LinearEquiv.apply_symm_apply] at e1
    simp only [g, LinearEquiv.trans_apply]
    rw [← e2, e1]
  refine ⟨G, ?_, fun w => ?_⟩
  · unfold IsSymp
    refine Matrix.map_injective hAinj ?_
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hGm]
    ext i j
    have key : ∀ s s' : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F,
        s ⬝ᵥ ((LinearMap.toMatrix' φ)ᵀ * weylM.map (algebraMap F (AF F)) * LinearMap.toMatrix' φ) *ᵥ s' =
          s ⬝ᵥ (weylM.map (algebraMap F (AF F))) *ᵥ s' := by
      intro s s'
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
        LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hφ, hφ, hstd, hkeep,
        ← hstd, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [single_dotProduct, Matrix.mulVec_single_one] using this
  · have := hact (c₁.e w)
    simpa [g] using this

end GlobalTheory.SympChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFiniteIdeleFactorizationStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_finite_idele_factorization : ∀ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∃ (r : ℚˣ) (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
    (u : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ ∧ ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ ∧
    t = Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom r * u := by
  first | exact @GlobalTheory.RatIdele.exists_rat_mul_intUnit | exact GlobalTheory.RatIdele.exists_rat_mul_intUnit | (intros; apply GlobalTheory.RatIdele.exists_rat_mul_intUnit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftReadingsScaleClassSumEigenspacesStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLift_readings_scale_classSum_eigenspaces : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : ℂ), GlobalTheory.Hk3.Core R F → IsStdChar D R.ψ (-1) → GlobalTheory.ConjScalar.ConjScalarAt R → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) → ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ (σ : D.what₂.LL →+* ℂ) (a : Pl D.host.E → List ℤ → D.what₂.LL), ∃ l : ℝ, ∀ x x' y y', GlobalTheory.ConjScalar.EigK R i a ((A.fam.L i A.μ0).toF ℓ Z x) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph ((A.fam.L i A.μ0).toF ℓ Z x) y → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x' y' → ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = (l : ℂ) * GlobalTheory.LiftLower.csumAt (A.fam.L i A.μ0).S σ ((A.fam.L i A.μ0).toF ℓ Z x) x' := by
  first | exact @GlobalTheory.ConjScalar.readings_scale_core | exact GlobalTheory.ConjScalar.readings_scale_core | (intros; apply GlobalTheory.ConjScalar.readings_scale_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedFinprodPureTensorAdelicSchwartzStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ f : SInf F κ, Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  first | exact @GlobalTheory.RestPure.rest_evI_finprod | exact GlobalTheory.RestPure.rest_evI_finprod | (intros; apply GlobalTheory.RestPure.rest_evI_finprod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartzStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_mem_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.AdelicCoordSB.finprod_mem_SB | exact GlobalTheory.AdelicCoordSB.finprod_mem_SB | (intros; apply GlobalTheory.AdelicCoordSB.finprod_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeCharacterTrivial
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.TraceDualChar

theorem psi_trivial_on_scaledInt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ z ∈ GlobalTheory.EvAdm.scaledInt F κ a,
      ψ (((0 : InfiniteAdeleRing F), ∑ i, z i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) = 1 := by
  intro F _ _ ψ hψ κ _ a _ b hb z hz

  have hrat : ∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
      ψ (((0 : InfiniteAdeleRing F), ∑ i, algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) = 1 := by
    intro ξ hξ
    obtain ⟨k, hk⟩ := hb ξ hξ
    set q : F := ∑ i, ξ i * b i with hq
    have e1 : (∑ i, algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) q := by
      rw [hq, map_sum]; simp only [map_mul]
    rw [e1]
    set y : AF F := (((algebraMap F (InfiniteAdeleRing F) q), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F) with hy
    have e2 : (show AF F from ((0 : InfiniteAdeleRing F), algebraMap F (FiniteAdeleRing (𝓞 F) F) q)) + y =
        algebraMap F (AF F) q := by
      rw [hy]
      show (show AF F from ((0 : InfiniteAdeleRing F) + algebraMap F (InfiniteAdeleRing F) q,
        algebraMap F (FiniteAdeleRing (𝓞 F) F) q + 0)) = algebraMap F (AF F) q
      rw [zero_add, add_zero]
      rfl
    have hAt : At (evI F) y := by
      intro u hu
      have hu1 : u.1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 this
      show (u.1 * algebraMap F (InfiniteAdeleRing F) q, u.2 * 0) = ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
      rw [hu1, zero_mul, mul_zero]
    have hev : evI F y = mixedEmbedding F q := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
      rfl
    have hyv : ψ y = 1 := by
      rw [hψ.2.2 y hAt, hev, GlobalTheory.PsiNontriv.trace_mixedEmbedding, hk]
      rw [show ((((k : ℚ) : ℝ) : ℂ)) = (k : ℂ) by push_cast; ring]
      rw [show -(2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-k)
    have h3 := congrArg ψ e2
    rw [AddChar.map_add_eq_mul, hyv, mul_one, hψ.2.1] at h3
    exact h3

  by_contra hne
  set G : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun z =>
    ψ (((0 : InfiniteAdeleRing F), ∑ i, z i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) with hG
  have hGc : Continuous G := by
    refine hψ.1.comp ?_
    refine Continuous.prodMk continuous_const ?_
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  have hU : IsOpen ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∩ G ⁻¹' {1}ᶜ) :=
    (GlobalTheory.EvAdm.isOpen_scaledInt a).inter (isOpen_compl_singleton.preimage hGc)
  have hd : DenseRange (fun ξ : κ → F => fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) :=
    DenseRange.piMap fun _ => GlobalTheory.AdeleCharTwist.denseRange_fin
  obtain ⟨ξ, hξ1, hξ2⟩ := hd.exists_mem_open hU ⟨z, hz, hne⟩
  exact hξ2 (hrat ξ hξ1)

end GlobalTheory.TraceDualChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchrSBFin

theorem isLocallyConstant_addChar {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  obtain ⟨U₀, hU₀⟩ := GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  filter_upwards [U₀.mem_nhds_zero] with s hs
  rw [AddChar.map_add_eq_mul, hU₀ s hs, mul_one]

theorem schr_mem_SB_of {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (ψ : AddChar K ℂ) (hψ : Continuous ψ) {κ : Type} [Fintype κ]
    (w : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → K)) :
    GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → K) := by
  obtain ⟨hlc, hcs⟩ := hφ
  have h1 : IsLocallyConstant fun x : κ → K => ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) :=
    (isLocallyConstant_addChar ψ hψ).comp_continuous
      ((continuous_id.dotProduct continuous_const).add continuous_const)
  have h2 : IsLocallyConstant fun x : κ → K => φ (x + w.1) := hlc.comp_continuous (continuous_add_right w.1)
  have h3 : HasCompactSupport fun x : κ → K => φ (x + w.1) := hcs.comp_homeomorph (Homeomorph.addRight w.1)
  exact ⟨h1.mul h2, h3.mul_left⟩

theorem schr_mem_SB : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ v ψ hψ κ _ w φ hφ
  exact schr_mem_SB_of ψ hψ w φ hφ

end GlobalTheory.SchrSBFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLatticeVacuumEigenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedingerOperator_heisenbergLatticeVacuum_eigen : ∀ {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, ∀ w ∈ Λ, ψ₀ (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) = 1) →
    ∀ w ∈ Λ, GlobalTheory.WeilM.schr ψ₀ w (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) = χ w • GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀ := by
  first | exact @GlobalTheory.HeisLatVac.schr_vacFn | exact GlobalTheory.HeisLatVac.schr_vacFn | (intros; apply GlobalTheory.HeisLatVac.schr_vacFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleSecondFiniteDatumIsFiniteRigging
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem _root_.GlobalTheory.T.seesawTriple_secondFiniteDatum_isFinite_rigging : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW), (∀ τ, (GlobalTheory.SquareComm.frSgn false FA').cart τ = X.rA'.s τ) → (∀ τ, FW.cart τ = X.rW.s τ) → X.Is ψ θ α β νH S → ∀ t, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW (X.f' t) := by
  intro D T A A' WW X ψ θ α β νH S FA' FW hA' hW hI t
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hth : IsThetaFunO ψ A' WW (X.f' t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hI.isVac'.1 hI.isVac'.2.inf (hI.snd t) hI.isVac'.2.theta
  refine ⟨hth, fun τ => ?_⟩
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hI.isVac'.1.1.1 hI.isVac'.2.inf ho.conj.infPart_eq
    ho.conj.conj.infPart_eq (hI.snd t) hI.isVac'.2.theta hth (hI.isVac'.2.fock τ)
  rw [hA' τ, hW τ]
  exact hF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGenericFibrePolarizationIsoStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_generic_fibre_polarization_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.admitted R (IsLocalRing.maximalIdeal R) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → GlobalTheory.LN.SplitOver G (IsLocalRing.maximalIdeal R) → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → (∃ (σ : LB.Sec P.L.L) (k : P.L.L.ι), σ.f k ≠ 0) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = P.L ∧ U.gen = gen := by
  first | exact @GlobalTheory.SectionUnif.exists_unif_of_ne_zero | exact GlobalTheory.SectionUnif.exists_unif_of_ne_zero | (intros; apply GlobalTheory.SectionUnif.exists_unif_of_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceNotNonsplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_place_not_nonsplit : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ G.pl.S0 → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  first | exact @GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt | exact GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt | (intros; apply GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt <;> assumption)
end

