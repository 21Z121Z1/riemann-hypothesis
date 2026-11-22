import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRepresentationEigenDecomposition
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmOrderActionDescendsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_order_action_descends : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ} {L : Set E}
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
  first | exact @GlobalTheory.LatModel.exists_lie_end_diagonal_of_tensor | exact GlobalTheory.LatModel.exists_lie_end_diagonal_of_tensor | (intros; apply GlobalTheory.LatModel.exists_lie_end_diagonal_of_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRepresentationEigenDecompositionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_representation_eigen_decomposition : ∀ (E : Type) [Field E] [NumberField E] (O : Subring E), (∀ x : E, ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ O) →
    ∀ (L : AddSubgroup E), (∀ a ∈ O, ∀ x ∈ L, a * x ∈ L) →
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (P : L →+ W), Submodule.span ℂ (Set.range P) = ⊤ →
      Module.finrank ℂ W = Module.finrank ℚ E →
    ∀ (T : O → Module.End ℂ W), (∀ (a : O) (x y : L), (y : E) = a * x → T a (P x) = P y) →
    ∀ τ : E →+* ℂ, Module.finrank ℂ (⨅ a : O, Module.End.eigenspace (T a) (τ a) : Submodule ℂ W) = 1 := by
  first | exact @GlobalTheory.EigLine.finrank_common_eigenspace_eq_one | exact GlobalTheory.EigLine.finrank_common_eigenspace_eq_one | (intros; apply GlobalTheory.EigLine.finrank_common_eigenspace_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeConjugateInFieldStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_conjugate_in_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (K : Type) [Field K] (j : K →+* ℂ) (I : Type)
    (φ : I → E →+* ℂ) (φK : I → E →+* K), (∀ i, j.comp (φK i) = φ i) → IsCMType φ →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMTypeIn (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
  first | exact @GlobalTheory.CMTypeThroughField.isCMTypeIn_bar | exact GlobalTheory.CMTypeThroughField.isCMTypeIn_bar | (intros; apply GlobalTheory.CMTypeThroughField.isCMTypeIn_bar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatingIntegerStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_separating_integer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i : I, ∃ b₀ : 𝓞 (FR E), ∀ j : I, φ j ((b₀ : FR E) : E) = φ i ((b₀ : FR E) : E) → j = i := by
  first | exact @GlobalTheory.CMSep.exists_int_sep_all | exact GlobalTheory.CMSep.exists_int_sep_all | (intros; apply GlobalTheory.CMSep.exists_int_sep_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleDescends
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatDescent

def restrictR {R D A E : Type} [CommRing R] [CommRing D] [CommRing A] [CommRing E]
    [Algebra R D] [Algebra R A] [Algebra R E] [Algebra D A] [Algebra D E]
    (hA : ∀ r, algebraMap D A (algebraMap R D r) = algebraMap R A r)
    (hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r)
    (f : A →ₐ[D] E) : A →ₐ[R] E :=
  ⟨f.toRingHom, fun r => by
    show f (algebraMap R A r) = algebraMap R E r
    rw [← hA r, ← hE r]; exact f.commutes _⟩

@[simp] theorem restrictR_apply {R D A E : Type} [CommRing R] [CommRing D] [CommRing A] [CommRing E]
    [Algebra R D] [Algebra R A] [Algebra R E] [Algebra D A] [Algebra D E]
    (hA : ∀ r, algebraMap D A (algebraMap R D r) = algebraMap R A r)
    (hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r)
    (f : A →ₐ[D] E) (x : A) : restrictR hA hE f x = f x := rfl

theorem cocycle_descends : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D'), (ψ : D →+* D').FaithfullyFlat → ∀ (c : ∀ (E : Type) [CommRing E] [Algebra R E], (D' →ₐ[R] E) → (D' →ₐ[R] E) → E), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (α β : D' →ₐ[R] E) (ρ : E →ₐ[R] E'), α.comp ψ = β.comp ψ → c E' (ρ.comp α) (ρ.comp β) = ρ (c E α β)) → (∀ (E : Type) [CommRing E] [Algebra R E] (f₁ f₂ f₃ : D' →ₐ[R] E), f₁.comp ψ = f₂.comp ψ → f₂.comp ψ = f₃.comp ψ → c E f₁ f₃ = c E f₁ f₂ + c E f₂ f₃) → ∃ a : D', ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → c E α β = β a - α a := by
  intro R _ D D' _ _ _ _ ψ hψ c hnat hcoc
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  letI instRT : Algebra R (D' ⊗[D] D') :=
    ((algebraMap D (D' ⊗[D] D')).comp (algebraMap R D)).toAlgebra
  have h' : ∀ r, algebraMap D D' (algebraMap R D r) = algebraMap R D' r := fun r => ψ.commutes r
  have hT : ∀ r, algebraMap D (D' ⊗[D] D') (algebraMap R D r) = algebraMap R (D' ⊗[D] D') r :=
    fun _ => rfl
  let i₁ : D' →ₐ[R] D' ⊗[D] D' := restrictR h' hT Algebra.TensorProduct.includeLeft
  let i₂ : D' →ₐ[R] D' ⊗[D] D' := restrictR h' hT Algebra.TensorProduct.includeRight
  have h12 : i₁.comp ψ = i₂.comp ψ := by
    ext d
    exact ((Algebra.TensorProduct.includeLeft (R := D) (S := D) (A := D') (B := D')).commutes d).trans
      ((Algebra.TensorProduct.includeRight (R := D) (A := D') (B := D')).commutes d).symm
  obtain ⟨a, ha⟩ := GlobalTheory.AmitsurCohomologyH1.cocycle_is_coboundary D D' (c (D' ⊗[D] D') i₁ i₂) (by
    intro E _ _ f₁ f₂ f₃
    letI : Algebra R E := ((algebraMap D E).comp (algebraMap R D)).toAlgebra
    have hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r := fun _ => rfl
    have key : ∀ f g : D' →ₐ[D] E,
        Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _) (c (D' ⊗[D] D') i₁ i₂) =
          c E (restrictR h' hE f) (restrictR h' hE g) := by
      intro f g
      let ρ : D' ⊗[D] D' →ₐ[R] E :=
        restrictR hT hE (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _))
      have hn := hnat (D' ⊗[D] D') E i₁ i₂ ρ h12
      have e1 : ρ.comp i₁ = restrictR h' hE f := by
        ext x; simp [ρ, i₁]
      have e2 : ρ.comp i₂ = restrictR h' hE g := by
        ext x; simp [ρ, i₂]
      rw [e1, e2] at hn
      exact hn.symm
    have hc : ∀ f g : D' →ₐ[D] E, (restrictR h' hE f).comp ψ = (restrictR h' hE g).comp ψ := by
      intro f g; ext d
      exact (f.commutes d).trans (g.commutes d).symm
    rw [key, key, key]
    exact hcoc E _ _ _ (hc _ _) (hc _ _))
  refine ⟨a, ?_⟩
  intro E _ _ α β hαβ
  letI : Algebra D E := ((α.comp ψ : D →ₐ[R] E) : D →+* E).toAlgebra
  let α' : D' →ₐ[D] E := ⟨α.toRingHom, fun _ => rfl⟩
  let β' : D' →ₐ[D] E := ⟨β.toRingHom, fun d => by
    show β (ψ d) = α (ψ d)
    exact (DFunLike.congr_fun hαβ d).symm⟩
  have hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r := fun r => by
    show α (ψ _) = _
    rw [ψ.commutes, α.commutes]
  let ρ : D' ⊗[D] D' →ₐ[R] E :=
    restrictR hT hE (Algebra.TensorProduct.lift α' β' (fun _ _ ↦ Commute.all _ _))
  have hn := hnat (D' ⊗[D] D') E i₁ i₂ ρ h12
  have e1 : ρ.comp i₁ = α := by
    ext x; simp [ρ, i₁, α']
  have e2 : ρ.comp i₂ = β := by
    ext x; simp [ρ, i₂, β']
  rw [e1, e2] at hn
  rw [hn]
  show Algebra.TensorProduct.lift α' β' (fun _ _ ↦ Commute.all _ _) (c (D' ⊗[D] D') i₁ i₂) = _
  rw [ha]
  simp [α', β']

end GlobalTheory.FlatDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValue
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.lift_coc : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) (D : Type) [CommRing D] [Algebra R D] (φ ψ : G.A n →ₐ[R] D), Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) = d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) - ((fv d.f (G.A n) D (toConv φ * toConv ψ).ofConv (t.y n) + (toConv φ * toConv ψ).ofConv (d.h n)) - (fv d.f (G.A n) D φ (t.y n) + φ (d.h n)) - (fv d.f (G.A n) D ψ (t.y n) + ψ (d.h n))) := by
  intro R _ A _ p G t c d n D _ _ φ ψ
  set l : G.A n ⊗[R] G.A n →ₐ[R] D := Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _) with hl
  have hc := (GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq R A d.f).1
  have e1 : l.comp Algebra.TensorProduct.includeLeft = φ := by
    ext a; simp [hl]
  have e2 : l.comp Algebra.TensorProduct.includeRight = ψ := by
    ext a; simp [hl]
  have e3 : l.comp (Bialgebra.comulAlgHom R (G.A n)) = (toConv φ * toConv ψ).ofConv := by
    ext a; rw [AlgHom.convMul_apply]; rfl
  have e4 : (toConv (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) *
      toConv Algebra.TensorProduct.includeRight).ofConv = Bialgebra.comulAlgHom R (G.A n) := by
    ext a; rw [AlgHom.convMul_apply]; simp
  have m := t.mul n (G.A n ⊗[R] G.A n) (toConv Algebra.TensorProduct.includeLeft)
    (toConv Algebra.TensorProduct.includeRight)
  rw [e4] at m
  have a := d.add (G.A n ⊗[R] G.A n) D l (spOver Algebra.TensorProduct.includeLeft ≫ t.y n)
    (spOver Algebra.TensorProduct.includeRight ≫ t.y n)
  have c1 := hc _ _ _ Algebra.TensorProduct.includeLeft l (t.y n) (sm_whole _)
  have c2 := hc _ _ _ Algebra.TensorProduct.includeRight l (t.y n) (sm_whole _)
  have c3 := hc _ _ _ (Bialgebra.comulAlgHom R (G.A n)) l (t.y n) (sm_whole _)
  rw [← m, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp, e1, e2] at a
  rw [e1] at c1
  rw [e2] at c2
  rw [e3] at c3
  have h3 : l (Coalgebra.comul (d.h n)) = (toConv φ * toConv ψ).ofConv (d.h n) := by
    rw [← e3]; rfl
  have h1 : l (d.h n ⊗ₜ 1) = φ (d.h n) := by simp [hl]
  have h2 : l (1 ⊗ₜ d.h n) = ψ (d.h n) := by simp [hl]
  simp only [Dat.coc, cobOne_apply, map_sub, h1, h2, h3]
  rw [c1, c2, c3]
  linear_combination -a

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSingleDerivationTaylorPowerSeries
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

theorem list_foldr_iterate_single_of_nodup {A : Type} {n : ℕ} (d : Fin n → A → A) (j : Fin n) (f : A) :
    ∀ l : List (Fin n), l.Nodup →
      l.foldr (fun i g => (d i)^[(Finsupp.single j 1 : Fin n →₀ ℕ) i] g) f = if j ∈ l then d j f else f := by
  intro l hl
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldr_cons, ih hl.2]
    by_cases hij : i = j
    · subst hij
      simp [hl.1]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Finsupp.single_apply, hij, hji]

theorem taylor_coeff_single (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B)
    (ds : Fin n → Derivation ℤ A A) (j : Fin n) (f : A) :
    MvPowerSeries.coeff (Finsupp.single j 1) (taylor ev (fun i => ⇑(ds i)) f) = ev (ds j f) := by
  have hit : iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f = ds j f := by
    unfold iterOp
    rw [list_foldr_iterate_single_of_nodup _ j f _ (List.nodup_finRange n)]
    simp [List.mem_finRange]
  have hprod : (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ)) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [Finsupp.single_apply, h]
  show (∏ i, (((Finsupp.single j 1 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) (Finsupp.single j 1) f) = _
  rw [hit, hprod, inv_one, one_smul]

end GlobalTheory.FormalOrigin.Extend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB

namespace GlobalTheory.FlagZ.Loc

variable {N : ℕ} {T : Scheme.{0}}

def colSecOn (g : T ⟶ Sp ℤ) (V : T.Opens) (G : Matrix (Fin N) (Fin N) Γ(T, V)) (j : Fin N) :
    Γ((Scheme.Modules.pullback g).obj (Taut.stdE N), V) :=
  ∑ i, G i j • GlobalTheory.QCoh.pullbackSections g (Taut.stdE N) (by simp) (freeFrame (Sp ℤ) (Fin N) i)

def Adapted {ι : Type} (g : T ⟶ Sp ℤ)
    (fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N) (V : T.Opens)
    (G : ι → GL (Fin N) Γ(T, V)) : Prop :=
  ∀ (a : ι) (l : Fin (N + 1)), ∃ s : Fin l → Γ((fl' a).F l, V), IsFrame s ∧
    ∀ j, ((fl' a).ι l).app V (s j) = colSecOn g V (G a).1 (Fin.castLE l.is_le j)

end GlobalTheory.FlagZ.Loc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSpreadPointsEqSpreadRootStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_spread_points_eq_spread_root : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] [IsNoetherianRing T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (k : ℕ) (x x' : baseOver (Sp Ω) ⟶ A.A) (y y' : baseOver (Sp T) ⟶ P.A) (c : Tˣ), 1 ≤ k → x.left ≫ φ = spMap jT ≫ y.left → x'.left ≫ φ = spMap jT ≫ y'.left → y ^ k = 1 → y' ^ k = 1 → WeilIs A.A A.L k x x' (unitOn (Units.map jT.toMonoidHom c)) → WeilIs P.A P.L k y y' (unitOn c) := by
  first | exact @GlobalTheory.MumPair.weilIs_of_spread | exact GlobalTheory.MumPair.weilIs_of_spread | (intros; apply GlobalTheory.MumPair.weilIs_of_spread <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

def IsBC {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left) {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G) {p : ℕ} [Fact p.Prime]
    {y₀ : S.R →+* PadicAlgCl p} (ev : R →+* OO p) (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X) : Prop :=
  ∃ (ev₀ : R →+* u.V) (_ : IsLocalHom ev₀) (hD : IsPullDeg ev₀ D.toPre u.D.toPre)
    (bc : u.G ≅ (Over.pullback (specOf ev₀)).obj G),
    IsMonHom bc.hom ∧ IsPullUnif ev₀ hD bc U u.U ∧ (∀ χ, hD.xe (ε χ) = χ) ∧
    (∀ r, algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (ev₀ r)) = (ev r : PadicAlgCl p)) ∧
    ∃ t : u.A.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, t ≫ pullback.fst _ _ = u.φ ∧
      t ≫ FinalForm.φ = genMap u.U ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) ≫ gm

end GlobalTheory.Poinc.TestAtPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.ExpKernel

theorem fderiv_apply_eq_zero {g : ℕ} (h : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) (hc : ∀ t : ℂ, h (t • w) = h 0) :
    fderiv ℂ h 0 w = 0 := by
  by_cases hd : DifferentiableAt ℂ h 0
  · have hl : HasFDerivAt (fun t : ℂ => t • w) ((ContinuousLinearMap.id ℂ ℂ).smulRight w) 0 :=
      ((ContinuousLinearMap.id ℂ ℂ).smulRight w).hasFDerivAt
    have h0 : HasFDerivAt h (fderiv ℂ h 0) ((0 : ℂ) • w) := by rw [zero_smul]; exact hd.hasFDerivAt
    have h1 := h0.comp (0 : ℂ) hl
    have h2 : HasFDerivAt (fun t : ℂ => h (t • w)) (0 : ℂ →L[ℂ] ℂ) 0 := by
      simp only [hc]; exact hasFDerivAt_const _ _
    have := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) (h1.unique h2)
    simpa using this
  · rw [fderiv_zero_of_not_differentiableAt hd]; rfl

theorem kernel_isFullLattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
    SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e →
    ∃ Λ : Submodule ℤ (Fin g → ℂ), DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧
      ∀ z, e z = 1 ↔ z ∈ Λ := by
  intro X G _ _ g hG hg y e he
  obtain ⟨hadd, hsurj, hhol, hd1, hd2⟩ := he
  let A : Over (Sp ℂ) := (Over.pullback y).obj G
  letI : GrpObj A := Functor.grpObjObj
  let φ : A.left ⟶ G.left := pullback.fst G.hom y
  have hp : IsGrpPullback A G y φ := isGrpPullback_pullback G y
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hp
  have hgA : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 hg
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hgA
  obtain ⟨ht₁, ht₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hgA
  have inj : ∀ x x' : 𝟙_ (Over (Sp ℂ)) ⟶ A, x.left ≫ φ = x'.left ≫ φ → x = x' := fun x x' h =>
    Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w x']))
  have lift : ∀ x₀ : Over.mk y ⟶ G, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x.left ≫ φ = x₀.left := fun x₀ =>
    ⟨Over.homMk (hp.1.lift x₀.left (𝟙 _) ((Over.w x₀).trans (Category.id_comp _).symm)) (hp.1.lift_snd _ _ _),
      hp.1.lift_fst _ _ _⟩
  choose Φ hΦ using lift
  have Φmul : ∀ x x', Φ (x * x') = Φ x * Φ x' := fun x x' => inj _ _ (by
    rw [hΦ, ← hp.2 _ (Φ x) (Φ x') (pushPt hp.1.w (Φ x)) (pushPt hp.1.w (Φ x')) rfl rfl]
    exact mul_left_congr (Category.id_comp _).symm _ _ _ _ (hΦ x).symm (hΦ x').symm)
  have Φinj : Function.Injective Φ := fun x x' h => Over.OverMorphism.ext (by rw [← hΦ, ← hΦ, h])
  have Φone : Φ 1 = 1 := by
    have := Φmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (Φ (e z)).left) :=
    FibreUnif.isHolTo_of_isPullback hp.1 (e := fun z => (Φ (e z)).left) (fun z => Over.w (Φ (e z)))
      (by simpa only [hΦ] using hhol)
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA L g g u ht₁ ht₂ (fun z => Φ (e z))
    (fun z z' => by rw [hadd, Φmul]) hol
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun w hw => by
    have hconst : ∀ t : ℂ, e (t • w) = e 0 := fun t => Φinj (by
      rw [← hF, ← hF, map_smul, hw, smul_zero, map_zero])
    have hiff : ∀ v, IsDerivAt0 (fun z => (e z).left) w v ↔ IsDerivAt0 (fun z => (e z).left) 0 v := by
      intro v
      unfold IsDerivAt0
      refine and_congr_right fun _ => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_
      rw [map_zero, fderiv_apply_eq_zero _ w (fun t => by simp only [hconst t, zero_smul])]
    obtain ⟨v, hv, -⟩ := hd1 w
    exact (hd2 v hv.1).unique hv ((hiff _).1 hv)
  let F' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofInjectiveEndo F Finj
  have hF' : ∀ z, F' z = F z := fun _ => rfl
  have hker : ∀ z, e z = 1 ↔ F z ∈ u.Λ := fun z => by
    rw [← u.ker, hF, ← Φone, Φinj.eq_iff]
  let Λ : Submodule ℤ (Fin g → ℂ) := u.Λ.comap F.toAddMonoidHom.toIntLinearMap
  have hmem : ∀ z, z ∈ Λ ↔ F z ∈ u.Λ := fun _ => Iff.rfl
  refine ⟨Λ, ?_, ?_, fun z => (hker z).trans (hmem z).symm⟩
  · have := u.discrete
    let c : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := F'.toContinuousLinearEquiv
    let f : Λ → u.Λ := fun x => ⟨F x, (hmem x).1 x.2⟩
    have hcomp : (Subtype.val ∘ f) = c ∘ (Subtype.val : Λ → Fin g → ℂ) := rfl
    have hemb : Topology.IsEmbedding f := by
      rw [← Topology.IsEmbedding.subtypeVal.of_comp_iff, hcomp]
      exact c.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    exact hemb.discreteTopology
  · let Fr : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := F'.restrictScalars ℝ
    have hset : (Λ : Set (Fin g → ℂ)) = Fr.symm '' (u.Λ : Set (Fin g → ℂ)) := by
      rw [LinearEquiv.image_symm_eq_preimage]
      ext z
      exact hmem z
    rw [hset, ← LinearEquiv.coe_coe, Submodule.span_image, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact Fr.symm.surjective

end GlobalTheory.ExpKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexMultiplicationDeRhamFormStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_multiplication_de_rham_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (𝔠 : FracId (FR E))
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (cm : OAct (orderC c) X₀.A),
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)),
    (∀ (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X₀.A)), IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c) ψ →
      ∃ (n : ℕ) (t : 𝓞 (FR E)), n ≠ 0 ∧ ∀ x y, (n : R) * ψ x y = ψ₀ x (act (dp0 R) (𝟙 _) X₀.rm t y)) →
    ∀ (I : Type) [Fintype I] (D : R) (N : I → Module.End K (K ⊗[R] (Fin n → R))) (M : I → Module.End R (Fin n → R)),
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsScaledRestr D (N i) (M i)) →
    (∀ i (a : OF E), Commute (N i) (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a)).baseChange K)) →
    (∀ i j, N i * N j = 0) →
    (∀ i x y, LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) (N i x) y + LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) x (N i y) = 0) →
    (∀ i j x y, LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) (N i x) (N j y) = 0) → admitted X₀ (fun i ↦ eH.symm.conjRingEquiv (M i)) := by
  first | exact @GlobalTheory.AdmTransport.admissible_transport_equiv | exact GlobalTheory.AdmTransport.admissible_transport_equiv | (intros; apply GlobalTheory.AdmTransport.admissible_transport_equiv <;> assumption)
end

