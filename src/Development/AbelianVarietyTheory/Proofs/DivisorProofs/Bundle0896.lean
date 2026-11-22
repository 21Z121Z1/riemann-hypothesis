import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0875
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGeneratorOfTrivialOnOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PicGlue

theorem stalkMap_gm {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (u : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U u) = gm (f ≫ g) z U u := by
  by_cases h : g (f z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val g (f z) U h, gm_val (f ≫ g) z U h]
    exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).trans rfl
  · have h' : (f ≫ g) z ∉ U := h
    simp only [gm, dif_neg h, dif_neg h', MonoidHom.one_apply, map_one]

theorem rigOn_of_triv_open : ∀ (X Y : Scheme.{0}) (e : Y ⟶ X) (V : Y.Opens) (L : LB X),
    (∀ (a : L.ι) (y : Y), e y ∈ L.U a → y ∈ V) → Triv (L.pull (V.ι ≫ e)) → ∃ r : RigD e L, RigOn e L r := by
  intro X Y e V L hV ⟨t, ht⟩
  have hle : ∀ a : L.ι, e ⁻¹ᵁ L.U a ≤ V.ι ''ᵁ (L.pull (V.ι ≫ e)).U (fun _ => a) := by
    intro a y hy
    obtain ⟨v, rfl⟩ : y ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hV a y hy
    exact V.ι.apply_mem_image_iff.2 (mem_pull.2 hy)
  refine ⟨fun a => res (hle a) (GlobalTheory.GlueLineBundle.imU V.ι _ (t.s fun _ => a)), ?_⟩
  intro y a b ha hb
  obtain ⟨v, rfl⟩ : y ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hV a y ha
  have key : ∀ c : L.ι, e (V.ι v) ∈ L.U c →
      gm V.ι v (e ⁻¹ᵁ L.U c) (res (hle c) (GlobalTheory.GlueLineBundle.imU V.ι _ (t.s fun _ => c))) =
        gm (𝟙 V.toScheme) v _ (t.s fun _ => c) := by
    intro c hc
    have hm : (𝟙 V.toScheme) v ∈ (L.pull (V.ι ≫ e)).U (fun _ => c) := mem_pull.2 hc
    rw [gm_res V.ι v (hle c) (show V.ι v ∈ e ⁻¹ᵁ L.U c from hc)]
    have := GlobalTheory.GlueLineBundle.gm_imU V.ι (𝟙 V.toScheme) v _ hm (t.s fun _ => c)
    rwa [Category.id_comp] at this
  have hinj : Function.Injective (Units.map (V.ι.stalkMap v).hom.toMonoidHom) :=
    Units.map_injective (asIso (V.ι.stalkMap v)).commRingCatIsoToRingEquiv.injective
  apply hinj
  rw [map_mul, stalkMap_gm, stalkMap_gm, stalkMap_gm, Category.comp_id]
  beta_reduce
  rw [key a ha, key b hb,
    (isGen_iff_germ t).1 ht v (fun _ => a) (fun _ => b) (mem_pull.2 ha) (mem_pull.2 hb),
    gm_pull_g L (V.ι ≫ e) (𝟙 V.toScheme) v (fun _ => a) (fun _ => b) (mem_pull.2 ha) (mem_pull.2 hb),
    Category.id_comp]

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankIdempotentMatrixLocalRingMapFieldStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_idempotent_matrix_local_ring_map_field : ∀ (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ) (Q : Matrix (Fin n) (Fin n) W), Q * Q = Q → ∃ r : ℕ, ∀ (k : Type) [Field k] (β : W →+* k), (Q.map β).rank = r := by
  first | exact @GlobalTheory.IdemRankLocal.rank_map_const | exact GlobalTheory.IdemRankLocal.rank_map_const | (intros; apply GlobalTheory.IdemRankLocal.rank_map_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemesStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∃ act' : O → (G' ⟶ G'), ((∀ a, IsMonHom (act' a)) ∧ act' 1 = 𝟙 G' ∧ (∀ a b, act' (a * b) = act' a ≫ act' b) ∧ (∀ a b, act' (a + b) = act' a * act' b)) ∧ ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := by
  first | exact @GlobalTheory.ActPull.exists_act_pull | exact GlobalTheory.ActPull.exists_act_pull | (intros; apply GlobalTheory.ActPull.exists_act_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOrderPiMatrixEmbeddings
section
noncomputable section

namespace GlobalTheory.UPel.HT.SplitC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix TensorProduct
open GlobalTheory.UPel.HT

theorem span_embeddings_eq_top (K : Type) [Field K] [NumberField K] :
    Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K)) = ⊤ := by
  rw [eq_top_iff, ← (canonicalEmbedding.latticeBasis K).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨RingOfIntegers.basis K i, ?_⟩
  rw [canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  rfl

theorem mem_of_embeddings {K : Type} [Field K] [NumberField K] {W : Type} [AddCommGroup W] [Module ℂ W]
    (V : Submodule ℂ W) (L : ((K →+* ℂ) → ℂ) → W) (hadd : ∀ f g, L (f + g) = L f + L g)
    (hsmul : ∀ (a : ℂ) f, L (a • f) = a • L f) (h : ∀ c : 𝓞 K, L (fun τ => τ (c : K)) ∈ V)
    (f : (K →+* ℂ) → ℂ) : L f ∈ V := by
  let Ll : ((K →+* ℂ) → ℂ) →ₗ[ℂ] W := { toFun := L, map_add' := hadd, map_smul' := hsmul }
  have hf : f ∈ Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K)) := by
    rw [span_embeddings_eq_top]; trivial
  have : Ll f ∈ (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll :=
    Submodule.mem_map_of_mem hf
  have hle : (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll ≤ V := by
    rw [Submodule.map_span_le]
    rintro _ ⟨c, rfl⟩
    exact h c
  exact hle this

variable {p : ℕ} [Fact p.Prime]

def padicToComplex (j : PadicAlgCl p ≃+* ℂ) : ℤ_[p] →+* ℂ :=
  j.toRingHom.comp ((algebraMap ℚ_[p] (PadicAlgCl p)).comp PadicInt.Coe.ringHom)

def evalTensor (F : Type) [Field F] (κ : ℤ_[p] →+* ℂ) (τ : F →+* ℂ) : 𝓞 F ⊗[ℤ] ℤ_[p] →+* ℂ :=
  (Algebra.TensorProduct.lift (τ.comp (algebraMap (𝓞 F) F)).toIntAlgHom κ.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

theorem evalTensor_tmul (F : Type) [Field F] (κ : ℤ_[p] →+* ℂ) (τ : F →+* ℂ) (c : 𝓞 F) (z : ℤ_[p]) :
    evalTensor F κ τ (c ⊗ₜ z) = τ (c : F) * κ z := by
  simp [evalTensor]

def bigPhi (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) :
    (D.O ⊗[ℤ] ℤ_[p]) →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) :=
  Pi.ringHom fun τ => (evalTensor D.F κ τ).mapMatrix.comp e.toRingHom

theorem bigPhi_algebraMap (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (c : 𝓞 D.F) (τ : D.F →+* ℂ) :
    bigPhi D κ e (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1) τ = Matrix.scalar (Fin D.m) (τ (c : D.F)) := by
  have h1 : (algebraMap (𝓞 D.F) D.O c ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c := rfl
  rw [h1]
  show (evalTensor D.F κ τ).mapMatrix (e (algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c)) = _
  rw [e.commutes c, Matrix.algebraMap_eq_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.scalar_apply, Algebra.TensorProduct.algebraMap_apply, evalTensor_tmul]
  split_ifs <;> simp [evalTensor_tmul]

theorem tmul_one_comm {A : Type} [Ring A] (z : ℤ_[p]) (a : A ⊗[ℤ] ℤ_[p]) :
    a * ((1 : A) ⊗ₜ z) = ((1 : A) ⊗ₜ z) * a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

theorem bigPhi_one_tmul (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (z : ℤ_[p]) :
    ∃ w : 𝓞 D.F ⊗[ℤ] ℤ_[p], bigPhi D κ e ((1 : D.O) ⊗ₜ z) = fun τ => Matrix.scalar (Fin D.m) (evalTensor D.F κ τ w) := by
  have hc : e ((1 : D.O) ⊗ₜ z) ∈ Set.center (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) := by
    rw [Semigroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, tmul_one_comm]
  rw [Matrix.center_eq_range] at hc
  obtain ⟨w, hw⟩ := hc
  refine ⟨w, funext fun τ => ?_⟩
  show (evalTensor D.F κ τ).mapMatrix (e ((1 : D.O) ⊗ₜ z)) = _
  rw [← hw]
  ext i j
  simp only [Matrix.scalar_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem mem_span_bigPhi (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (y : D.O ⊗[ℤ] ℤ_[p]) :
    bigPhi D κ e y ∈ Submodule.span ℂ (Set.range ((bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom)) := by
  set V := Submodule.span ℂ (Set.range ((bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom))
  have hφ : ∀ x : D.O, bigPhi D κ e (x ⊗ₜ 1) ∈ V := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hL : ∀ (x : D.O) (f : (D.F →+* ℂ) → ℂ),
      (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1) ∈ V := by
    intro x
    apply mem_of_embeddings V (fun f => (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1))
    · intro f g
      funext τ
      simp only [Pi.mul_apply, Pi.add_apply, map_add, _root_.add_mul]
    · intro a f
      funext τ
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_mul, _root_.mul_assoc]
    · intro c
      have : (fun τ : D.F →+* ℂ => Matrix.scalar (Fin D.m) (τ (c : D.F))) =
          bigPhi D κ e (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1) := funext fun τ => (bigPhi_algebraMap D κ e c τ).symm
      rw [this, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
      exact hφ _
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x z =>
    obtain ⟨w, hw⟩ := bigPhi_one_tmul D κ e z
    have : x ⊗ₜ[ℤ] z = ((1 : D.O) ⊗ₜ z) * (x ⊗ₜ 1) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
    rw [this, map_mul, hw]
    exact hL x _
  | add a b ha hb => rw [map_add]; exact V.add_mem ha hb

theorem bigPhi_symm_single (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (i j : Fin D.m) (c : 𝓞 D.F) :
    bigPhi D κ e (e.symm (Matrix.single i j (c ⊗ₜ 1))) = fun τ => Matrix.single i j (τ (c : D.F)) := by
  funext τ
  show (evalTensor D.F κ τ).mapMatrix (e (e.symm _)) = _
  rw [e.apply_symm_apply]
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [evalTensor_tmul]

theorem exists_ringHom_pi_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p),
    ∃ φ : D.O →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ),
      (∀ (c : 𝓞 D.F) τ, φ (algebraMap (𝓞 D.F) D.O c) τ = Matrix.scalar (Fin D.m) (τ (c : D.F))) ∧
        Submodule.span ℂ (Set.range φ) = ⊤ := by
  intro p _ D
  obtain ⟨e⟩ := D.splitP
  obtain ⟨j⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p
  set κ := padicToComplex j
  refine ⟨(bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom, fun c τ => bigPhi_algebraMap D κ e c τ, ?_⟩
  rw [eq_top_iff]
  intro X _
  have hX : X = ∑ i, ∑ k, (fun τ => Matrix.single i k (X τ i k)) := by
    funext τ
    simp only [Finset.sum_apply]
    exact Matrix.matrix_eq_sum_single (X τ)
  rw [hX]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ => ?_
  apply mem_of_embeddings _ (fun f => fun τ => Matrix.single i k (f τ)) (f := fun τ => X τ i k)
  · intro f g; funext τ; simp [Matrix.single_add]
  · intro a f; funext τ; simp [Matrix.smul_single]
  · intro c
    rw [← bigPhi_symm_single D κ e i k c]
    exact mem_span_bigPhi D κ e _

end GlobalTheory.UPel.HT.SplitC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareGroupSchemePullbackStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_group_scheme_pullback : ∀ (S S₀ : Scheme.{0}) (f : S₀ ⟶ S) (B : Over S) [GrpObj B] (B₀ : Over S₀) [GrpObj B₀] (i : B₀.left ⟶ B.left), IsGrpPullback B₀ B f i → ∃ k : (B₀ ⊗ B₀).left ⟶ (B ⊗ B).left, IsPullback k (B₀ ⊗ B₀).hom (B ⊗ B).hom f ∧ k ≫ (μ[B]).left = (μ[B₀]).left ≫ i ∧ k ≫ (fst B B).left = (fst B₀ B₀).left ≫ i ∧ k ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
  first | exact @GlobalTheory.SqPull.sq_of_grpPullback | exact GlobalTheory.SqPull.sq_of_grpPullback | (intros; apply GlobalTheory.SqPull.sq_of_grpPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
section
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory.SchwartzMajorant

variable (F : Type) [Field F] [NumberField F]

theorem pureA_add_algebraMap {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (ξ : κ → F) (x : κ → AdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.pureA F f g (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j) =
      f ((fun j => mixedEmbedding F (ξ j)) + fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1) *
      g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + fun j => (x j).2) := by
  unfold GlobalTheory.WeilM.pureA
  congr 2
  funext j
  simp only [Pi.add_apply]
  rw [show (algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j).1 = (algebraMap F (AdeleRing (𝓞 F) F) (ξ j)).1 + (x j).1 from rfl,
    map_add, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem norm_le_of_decay {V : Type} [NormedAddCommGroup V] {φ : V → ℂ} {k : ℕ} {C0 Ck : ℝ}
    (h0 : ∀ v, ‖φ v‖ ≤ C0) (hk : ∀ v, ‖v‖ ^ k * ‖φ v‖ ≤ Ck) (w a : V) :
    ‖φ (w + a)‖ * (1 + ‖w‖) ^ k ≤ 2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k := by
  set u := w + a with hu
  have hCk : 0 ≤ Ck := le_trans (by positivity) (hk 0)
  have hC0 : 0 ≤ C0 := le_trans (norm_nonneg _) (h0 0)
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have h1 : ‖φ u‖ * (1 + ‖u‖) ^ k ≤ 2 ^ k * (C0 + Ck) := by
    rcases le_total ‖u‖ 1 with hu1 | hu1
    · calc ‖φ u‖ * (1 + ‖u‖) ^ k ≤ C0 * 2 ^ k :=
            mul_le_mul (h0 u) (pow_le_pow_left₀ (by positivity) (by linarith) k) (by positivity) hC0
        _ ≤ _ := by nlinarith
    · calc ‖φ u‖ * (1 + ‖u‖) ^ k ≤ ‖φ u‖ * (2 * ‖u‖) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k) (norm_nonneg _)
        _ = 2 ^ k * (‖u‖ ^ k * ‖φ u‖) := by rw [mul_pow]; ring
        _ ≤ 2 ^ k * Ck := mul_le_mul_of_nonneg_left (hk u) h2k.le
        _ ≤ _ := by nlinarith
  have h2 : (1 + ‖w‖) ^ k ≤ (1 + ‖a‖) ^ k * (1 + ‖u‖) ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : ‖w‖ ≤ ‖u‖ + ‖a‖ := by
      calc ‖w‖ = ‖u - a‖ := by rw [hu, add_sub_cancel_right]
        _ ≤ ‖u‖ + ‖a‖ := norm_sub_le _ _
    nlinarith [norm_nonneg u, norm_nonneg a]
  calc ‖φ u‖ * (1 + ‖w‖) ^ k ≤ ‖φ u‖ * ((1 + ‖a‖) ^ k * (1 + ‖u‖) ^ k) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = (‖φ u‖ * (1 + ‖u‖) ^ k) * (1 + ‖a‖) ^ k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

theorem summable_one_add_norm_pow_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), inv_pow]
  exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)

theorem exists_majorant_pureA {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (x : κ → AdeleRing (𝓞 F) F) :
    ∃ k : ℕ, ∃ M : (κ → F) → ℝ, Summable M ∧ ∀ (C0 Ck : ℝ) (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
      (∀ v, ‖φ v‖ ≤ C0) → (∀ v, ‖v‖ ^ k * ‖φ v‖ ≤ Ck) → ∀ ξ : κ → F,
        ‖GlobalTheory.WeilM.pureA F φ g (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ (C0 + Ck) * M ξ := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  let xf : κ → FiniteAdeleRing (𝓞 F) F := fun j => (x j).2
  let a : κ → mixedEmbedding.mixedSpace F := fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1
  have hK : IsCompact ((fun y => y - xf) '' tsupport g) :=
    hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hKN⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hK
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  let v : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ j => mixedEmbedding F (ξ j)
  let S : Set (κ → F) := {ξ | v ξ ∈ GlobalTheory.WeilM.denomLattice F κ N}
  let k := Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1
  refine ⟨k, S.indicator fun ξ => 2 ^ k * (1 + ‖a‖) ^ k * B * ((1 + ‖v ξ‖) ^ k)⁻¹, ?_, ?_⟩
  · rw [← summable_subtype_iff_indicator]
    let j : S → GlobalTheory.WeilM.denomLattice F κ N := fun ξ => ⟨v ξ, ξ.2⟩
    have hj : Function.Injective j := fun p q h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    exact ((summable_one_add_norm_pow_inv (GlobalTheory.WeilM.denomLattice F κ N)).comp_injective hj).mul_left _
  · intro C0 Ck φ h0 hk ξ
    rw [pureA_add_algebraMap, norm_mul]
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ]
      have hd := norm_le_of_decay h0 hk (v ξ) a
      have hpos : 0 < (1 + ‖v ξ‖) ^ k := by positivity
      have h1 : ‖φ (v ξ + a)‖ ≤ 2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k * ((1 + ‖v ξ‖) ^ k)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hd
      calc ‖φ (v ξ + a)‖ * ‖g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf)‖
          ≤ (2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k * ((1 + ‖v ξ‖) ^ k)⁻¹) * B :=
            mul_le_mul h1 (hB _) (norm_nonneg _) (le_trans (norm_nonneg _) h1)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hξ, mul_zero]
      have hz : g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf) = 0 := by
        by_contra h0'
        apply hξ
        have hmem : (fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) ∈ (fun y => y - xf) '' tsupport g :=
          ⟨_, subset_tsupport _ h0', add_sub_cancel_right _ _⟩
        show ∀ i, (N : ℝ) • v ξ i ∈ mixedEmbedding.integerLattice F
        intro i
        obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun w => by
          rw [map_mul, map_natCast]
          exact hKN _ hmem i w
        refine ⟨y, ?_⟩
        have h2 := congrArg (mixedEmbedding F) hy
        rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
        exact h2.symm
      show _ * ‖g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf)‖ ≤ 0
      rw [hz, norm_zero, mul_zero]

theorem exists_summable_majorant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {P : Type}
    [TopologicalSpace P]
    (Ψ : P → (κ → AdeleRing (𝓞 F) F) → ℂ) (p0 : P) (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (f : P → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
    (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) →
    (∀ᶠ p in nhds p0, Ψ p = ∑ i, GlobalTheory.WeilM.pureA F (f p i) (g i)) →
    (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C) →
    ∀ x : κ → AdeleRing (𝓞 F) F, ∃ M : (κ → F) → ℝ, Summable M ∧
      ∀ᶠ p in nhds p0, ∀ ξ : κ → F, ‖Ψ p (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ M ξ := by
  intro F _ _ κ _ P _ Ψ p0 m g f hg hΨ hC x
  choose k M hM hbound using fun i => exists_majorant_pureA F (hg i) x
  choose C hCev using hC
  refine ⟨fun ξ => ∑ i, (C 0 + C (k i)) * M i ξ, summable_sum fun i _ => (hM i).mul_left _, ?_⟩
  have hall : ∀ᶠ p in nhds p0, ∀ i, (∀ v, ‖v‖ ^ 0 * ‖f p i v‖ ≤ C 0) ∧
      (∀ v, ‖v‖ ^ k i * ‖f p i v‖ ≤ C (k i)) :=
    Filter.eventually_all.2 fun i => ((hCev 0).and (hCev (k i))).mono fun p hp => ⟨hp.1 i, hp.2 i⟩
  filter_upwards [hΨ, hall] with p hp hb ξ
  rw [hp, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hbound i _ _ _ (fun v => ?_) (hb i).2 ξ)
  simpa using (hb i).1 v

end GlobalTheory.SchwartzMajorant
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroupStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∃ T : (Fin n → R') → (epsPtR (spMap β) ⟶ G), Function.Injective T ∧ (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c) := by
  first | (exact @GlobalTheory.LieCoordR.exists_coords_baseChange) | (exact GlobalTheory.LieCoordR.exists_coords_baseChange) | (intros; apply GlobalTheory.LieCoordR.exists_coords_baseChange  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTransitionUnitsCocycleThinBasisStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_transition_units_cocycle_thin_basis : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → IsCoc V hV u → ∀ T₁ T₂ : C, ∃! g : Γ(X, V T₁ ⊓ V T₂)ˣ, ∀ (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T), res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b := by
  first | exact @GlobalTheory.LBTrans.transition_units | exact GlobalTheory.LBTrans.transition_units | (intros; apply GlobalTheory.LBTrans.transition_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueUnitRatioGeneratorsIsomorphicLineBunStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_unit_ratio_generators_isomorphic_lineBundles : ∀ (X : Scheme.{0}) (L L' : LB X) (W : X.Opens) (w : LB.Iso L L') (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ) (τ' : ∀ m : L'.ι, Γ(X, W ⊓ L'.U m)ˣ), L.IsLB → L'.IsLB → w.IsGen → IsGenOn L W τ → IsGenOn L' W τ' → ∃! t : Γ(X, W)ˣ, ∀ (m : L.ι) (m' : L'.ι), res (inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W) t * res (inf_le_inf_left W inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L'.U m') (τ' m') = res (inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ L'.U m' ⊓ L.U m) (w.s (m', m)) * res (inf_le_inf_left W inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L.U m) (τ m) := by
  first | exact @GlobalTheory.GenRatio.exists_unique_ratio | exact GlobalTheory.GenRatio.exists_unique_ratio | (intros; apply GlobalTheory.GenRatio.exists_unique_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionPreservesAdelicMatricesStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_action_preserves_adelic_matrices : ∀ (K : Type) [Field K] [NumberField K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → IsAdelic fun w => fibA la (a w) (B w) := by
  first | exact @GlobalTheory.FibAdel.fibA_isAdelic | exact GlobalTheory.FibAdel.fibA_isAdelic | (intros; apply GlobalTheory.FibAdel.fibA_isAdelic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibrePowerMapOfTotalSpaces_isPullback : ∀ (S S' : Scheme.{0}) (A : Over S) (A' : Over S') (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (hφ : φ ≫ A.hom = A'.hom ≫ f), IsPullback φ A'.hom A.hom f → ∀ m : ℕ, IsPullback (powMap f φ hφ m) (pow A' m).hom (pow A m).hom f := by
  first | (exact @GlobalTheory.KS.PowPB.powMap_isPullback) | (exact GlobalTheory.KS.PowPB.powMap_isPullback) | (intros; apply GlobalTheory.KS.PowPB.powMap_isPullback  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproximationModConductorStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_approximation_mod_conductor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (y : (Af E)ˣ) (z : Af E), ∃ x : E, (z - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  first | exact @GlobalTheory.CMVal.ApproxHatO.exists_sub_mul_mem_hatO | exact GlobalTheory.CMVal.ApproxHatO.exists_sub_mul_mem_hatO | (intros; apply GlobalTheory.CMVal.ApproxHatO.exists_sub_mul_mem_hatO <;> assumption)
end

