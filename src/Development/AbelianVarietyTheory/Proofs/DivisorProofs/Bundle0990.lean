import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0962
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantMultilinearMapsSmoothVectorsIntertwin
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.SmoothMultilinear

theorem conj_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {g : Mt V.rank} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  have h1 := M.fr_gram τ
  have h2 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  show (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹) = Formalism.REAL.Jm (M.ε τ)
  calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by
        rw [h1, hg']
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h2]; simp

theorem rep_one {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    M.rep τ 1 = 1 := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  unfold DSModel.rep
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

theorem rep_mul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {a b : Mt V.rank} (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (a * b) = M.rep τ a * M.rep τ b := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h2 : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
  unfold DSModel.rep
  have e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = (M.fr τ * a * (M.fr τ)⁻¹) * (M.fr τ * b * (M.fr τ)⁻¹) := by
    calc _ = M.fr τ * a * ((M.fr τ)⁻¹ * M.fr τ) * b * (M.fr τ)⁻¹ := by
          rw [h2]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  exact (M.ds τ).2.2.1.1.2 _ (conj_mem M τ ha) _ (conj_mem M τ hb)

theorem prod_mem {n : ℕ} (H : Mt n) (l : List (Mt n)) (hl : ∀ g ∈ l, g ∈ Formalism.QuantumDeterminants.UH H) :
    l.prod ∈ Formalism.QuantumDeterminants.UH H := by
  induction l with
  | nil => show (1 : Mt n)ᴴ * H * 1 = H; simp
  | cons a l ih =>
    rw [List.prod_cons]
    exact CCRuleCW.UH_mul _ _ _ (hl a (by simp)) (ih fun g hg => hl g (by simp [hg]))

theorem exp_mem {n : ℕ} (H X : Mt n) (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  apply CCRuleCW.exp_mem_UH
  have := CCRuleCW.lie_smul H X hX t
  rwa [Complex.coe_smul] at this

theorem smooth_of_span {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Mt n)) (σ : Mt n → (H →L[ℂ] H)) (v : H) (hv : v ∈ Submodule.span ℂ {w | SmoothVec L σ w}) :
    SmoothVec L σ v := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro k Xs _; simp only [map_zero]; exact contDiff_const
  | add x y _ _ hx hy => intro k Xs h; simp only [map_add]; exact (hx k Xs h).add (hy k Xs h)
  | smul c x _ hx => intro k Xs h; simp only [map_smul]; exact (hx k Xs h).const_smul c

theorem hasDerivAt_of_smooth {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Mt n)) (σ : Mt n → (H →L[ℂ] H)) (v : H) (hv : SmoothVec L σ v) (X : Mt n) (hX : X ∈ L) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) (dRep σ X v) 0 := by
  have h := hv 1 (fun _ => X) (fun _ => hX)
  have h2 : ContDiff ℝ ∞ (fun t : ℝ => (fun _ : Fin 1 => t)) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := h.comp h2
  have h4 : ContDiff ℝ ∞ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) := by
    convert h3 using 2
    simp
  exact (h4.differentiable (by simp) 0).hasDerivAt

theorem act_list {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K)
    (h : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y))
    (y : ∀ τ, M.H τ) (l : List (D.what₂.Tau × Mt V.rank))
    (hl : ∀ p ∈ l, p.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V p.1)) :
    ρ (l.map fun p => atTau θ V p.1 p.2).prod (Φ y) =
      Φ fun τ => M.rep τ (l.map fun p => if p.1 = τ then p.2 else 1).prod (y τ) := by
  induction l with
  | nil => simp [rep_one]
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ Formalism.QuantumDeterminants.UH (gramAt D V q.1) := fun q hq => hl q (by simp [hq])
    rw [List.map_cons, List.prod_cons, map_mul, ContinuousLinearMap.mul_apply, ih hl',
      ← h p.1 p.2 (hl p (by simp))]
    congr 1
    funext τ
    rw [List.map_cons, List.prod_cons]
    by_cases e : p.1 = τ
    · subst e
      rw [Function.update_self, if_pos rfl, rep_mul M _ (hl p (by simp)), ContinuousLinearMap.mul_apply]
      apply prod_mem
      intro g hg
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
      split_ifs with e
      · exact e ▸ hl' q hq
      · exact prod_mem _ [] (by simp)
    · rw [Function.update_of_ne (Ne.symm e), if_neg e, one_mul]

theorem smooth_map : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K)) (Φ : ContinuousMultilinearMap ℂ M.H K), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) → ∀ v : M.Vec, IsSmoothVector' θ V ρ (Φ fun τ => (v τ : M.H τ)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) = Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))) := by
  intro D θ V _ S M K _ _ ρ Φ h v
  have hs : ∀ τ, SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) := fun τ => smooth_of_span _ _ _ (v τ).2
  refine ⟨?_, ?_⟩
  · intro k τs Xs hX
    have e : (fun t : Fin k → ℝ => ρ (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod (Φ fun τ => (v τ : M.H τ))) =
        fun t : Fin k → ℝ => Φ fun τ => M.rep τ
          (List.ofFn fun i => NormedSpace.exp (t i • (if τs i = τ then Xs i else 0))).prod (v τ : M.H τ) := by
      funext t
      have := act_list θ M ρ Φ h (fun τ => (v τ : M.H τ))
        (List.ofFn fun i => (τs i, NormedSpace.exp (t i • Xs i))) (by
          intro p hp
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
          exact exp_mem _ _ (hX i) _)
      simp only [List.map_ofFn] at this
      refine this.trans ?_
      congr 1
      funext τ
      congr 4
      funext i
      simp only [Function.comp]
      split_ifs <;> simp
    rw [e]
    have hΦ : ContDiff ℝ ∞ (Φ : (∀ τ, M.H τ) → K) := (Φ.contDiff (n := ∞)).restrict_scalars ℝ
    refine hΦ.comp (contDiff_pi.2 fun τ => ?_)
    refine hs τ k _ fun i => ?_
    split_ifs with e
    · exact e ▸ hX i
    · simp [lieAt]
  · intro τ X hX
    have e : (fun t : ℝ => ρ (oneP θ V τ X t) (Φ fun τ => (v τ : M.H τ))) =
        fun t : ℝ => (Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ)
          (M.rep τ (NormedSpace.exp (t • X)) (v τ)) := by
      funext t
      exact (h τ _ (exp_mem _ _ hX t) _).symm
    unfold dL2
    simp only
    rw [e]
    have h1 := hasDerivAt_of_smooth _ _ _ (hs τ) X hX
    exact (((Φ.toContinuousLinearMap (fun τ => (v τ : M.H τ)) τ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1).deriv

end GlobalTheory.SmoothMultilinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.LocGlobRing

noncomputable def pbIso (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    pullback g (Spec.map (CommRingCat.ofHom (algebraMap A O))) ≅ Spec (CommRingCat.of (O ⊗[A] X)) :=
  pullback.congrHom hg rfl ≪≫ pullbackSymmetry _ _ ≪≫ pullbackSpecIso A O X

theorem pbIso_inv_fst (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    (pbIso A X O g hg).inv ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : X →ₐ[A] O ⊗[A] X).toRingHom) := by
  subst hg
  simp [pbIso, pullback.congrHom_inv, pullbackSpecIso_inv_snd]

theorem pbIso_inv_snd (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    (pbIso A X O g hg).inv ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : O →+* O ⊗[A] X)) := by
  subst hg
  simp [pbIso, pullback.congrHom_inv, pullbackSpecIso_inv_fst]

end GlobalTheory.LocGlobRing

namespace GlobalTheory.LocGlobRing

theorem square (A B C O : Type) [CommRing A] [CommRing B] [CommRing C] [CommRing O] [Algebra A B] [Algebra A C] [Algebra A O]
    (φ : B →ₐ[A] C)
    (hC : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = Spec.map (CommRingCat.ofHom (algebraMap A C)))
    (h₁ h₂) :
    (pbIso A C O _ hC).inv ≫ pullback.map (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A O))) (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A O))) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 _) (𝟙 _) h₁ h₂ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) ≫ (pbIso A B O _ rfl).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pbIso_inv_fst, Category.assoc, pbIso_inv_fst,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, pbIso_inv_snd, Category.assoc, pbIso_inv_snd,
      ← Spec.map_comp]
    congr 1
    ext x
    simp

end GlobalTheory.LocGlobRing

theorem GlobalTheory.LocGlobRing.main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (φ : B →ₐ[A] C), (∀ (O : Type) [CommRing O] [Algebra A O], SH O → IndEt A O → Eqv R (spMap (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) F) → Eqv R (spMap φ.toRingHom) F := by
  intro R _ F hF A B C _ _ _ _ _ φ hyp
  have hC : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp
  refine GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks R F hF (Spec (CommRingCat.of C)) (Spec (CommRingCat.of B)) (Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Spec.map (CommRingCat.ofHom (algebraMap A B))) ?_
  intro O _ s hs
  obtain ⟨inst, hSH, hInd, rfl⟩ := GlobalTheory.T.isIndEtaleAlgebra_of_strictlyHenselianEtaleStalk_affine A O s hs
  have h := @hyp O _ inst hSH hInd
  have eb := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  rw [← Iso.hom_inv_id_assoc (GlobalTheory.LocGlobRing.pbIso A C O _ hC) (pullback.map _ _ _ _ _ _ _ _ _),
    GlobalTheory.LocGlobRing.square A B C O φ hC, Functor.map_comp, Functor.map_comp]
  exact (eb.2.1 _ _ _ _ _).1 (eb.1 _ _ _ inferInstance) ((eb.2.1 _ _ _ _ _).1 h (eb.1 _ _ _ inferInstance))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerContractionChartForms
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR.StabTheta

variable {K : Type} [Field K]

theorem smul_mem_spanForms (M M' : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ) (c : K)
    (h : ∀ m ∈ M, c * m ∈ M') {η : abelian₂ K} (hη : η ∈ spanForms M H a) :
    c • η ∈ spanForms M' H a := by
  have key : spanForms M H a ≤
      (spanForms M' H a).comap (DistribMulAction.toAddMonoidHom (abelian₂ K) c) := by
    unfold spanForms
    rw [AddSubgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show c • (m • ExteriorAlgebra.ιMulti K a v) ∈ AddSubgroup.closure _
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨c * m, h m hm, v, hv, rfl⟩
  exact key hη

theorem iota_mul_mem_spanForms (M : Set K) (H : Set Ω[K⁄ℤ]) (q : ℕ) (w : Ω[K⁄ℤ]) (hw : w ∈ H)
    {η : abelian₂ K} (hη : η ∈ spanForms M H q) :
    ExteriorAlgebra.ι K w * η ∈ spanForms M H (q + 1) := by
  have key : spanForms M H q ≤
      (spanForms M H (q + 1)).comap (AddMonoidHom.mulLeft (ExteriorAlgebra.ι K w)) := by
    unfold spanForms
    rw [AddSubgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show ExteriorAlgebra.ι K w * (m • ExteriorAlgebra.ιMulti K q v) ∈ AddSubgroup.closure _
    rw [mul_smul_comm]
    refine AddSubgroup.subset_closure ⟨m, hm, Fin.cons w v, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hw
      · simpa using hv k
    · rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp [Matrix.vecTail]
  exact key hη

theorem theta_dlog {n : ℕ} (x : Fin n → Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K)
    (hθ : IsEulerContraction x i θ) (j : Fin n) :
    θ (ExteriorAlgebra.ι K (dlog (x j))) = algebraMap K (abelian₂ K) (if j = i then 1 else 0) := by
  rw [hθ.2.2 j]
  split_ifs <;> simp

theorem theta_frame (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hx : ∀ j, (x j : K) ∈ A) (hθ : IsEulerContraction x i θ) (j : Fin n) :
    ∃ a ∈ A, θ (ExteriorAlgebra.ι K (frame x J j)) = algebraMap K (abelian₂ K) a := by
  have hif : (if j = i then (1 : K) else 0) ∈ A := by split_ifs <;> simp
  unfold frame
  split_ifs with hj
  · exact ⟨_, hif, theta_dlog x i θ hθ j⟩
  · have hd : dK (x j : K) = (x j : K) • dlog (x j) := by
      unfold dlog
      rw [smul_smul]
      simp
    refine ⟨(x j : K) * (if j = i then 1 else 0), A.mul_mem (hx j) hif, ?_⟩
    rw [hd, map_smul, map_smul, theta_dlog x i θ hθ j, Algebra.smul_def, ← map_mul]

theorem theta_iotaMulti (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hx : ∀ j, (x j : K) ∈ A) (hθ : IsEulerContraction x i θ) :
    ∀ (q : ℕ) (v : Fin (q + 1) → Ω[K⁄ℤ]), (∀ k, v k ∈ Set.range (frame x J)) →
      θ (ExteriorAlgebra.ιMulti K (q + 1) v) ∈ spanForms (A : Set K) (Set.range (frame x J)) q := by
  intro q
  induction q with
  | zero =>
    intro v hv
    rw [ExteriorAlgebra.ιMulti_succ_apply, hθ.2.1, ExteriorAlgebra.ιMulti_zero_apply, hθ.1,
      mul_zero, sub_zero, mul_one]
    obtain ⟨j, hj⟩ := hv 0
    obtain ⟨a, ha, he⟩ := theta_frame A x J i θ hx hθ j
    rw [← hj, he, Algebra.algebraMap_eq_smul_one]
    refine AddSubgroup.subset_closure ⟨a, ha, Matrix.vecTail v, fun k => k.elim0, ?_⟩
    rw [ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    intro v hv
    rw [ExteriorAlgebra.ιMulti_succ_apply, hθ.2.1]
    obtain ⟨j, hj⟩ := hv 0
    obtain ⟨a, ha, he⟩ := theta_frame A x J i θ hx hθ j
    have htail : ∀ k, Matrix.vecTail v k ∈ Set.range (frame x J) := fun k => hv k.succ
    refine AddSubgroup.sub_mem _ ?_ ?_
    · rw [← hj, he, ← Algebra.smul_def]
      exact AddSubgroup.subset_closure ⟨a, ha, Matrix.vecTail v, htail, rfl⟩
    · exact iota_mul_mem_spanForms _ _ q _ (hv 0) (ih _ htail)

end GlobalTheory.LogDR.StabTheta

open GlobalTheory.LogDR.StabTheta in
theorem GlobalTheory.LogDR.chartForms_stable_euler :
    ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K), (∀ j, (x j : K) ∈ A) → IsEulerContraction x i θ → (∀ q, ∀ η ∈ chartForms A x J t (q + 1), θ η ∈ chartForms A x J t q) ∧ ∀ η ∈ chartForms A x J t 0, θ η = 0 := by
  intro K _ A n x J t i θ hx hθ
  constructor
  · intro q η hη
    have key : chartForms A x J t (q + 1) ≤ (chartForms A x J t q).comap θ.toAddMonoidHom := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show θ (c • ExteriorAlgebra.ιMulti K (q + 1) v) ∈ spanForms _ _ q
      rw [map_smul]
      refine smul_mem_spanForms (A : Set K) _ _ q c ?_ (theta_iotaMulti A x J i θ hx hθ q v hv)
      intro m hm
      show c * m * (t : K) ∈ A
      rw [mul_right_comm]
      exact A.mul_mem hc hm
    exact key hη
  · intro η hη
    have key : chartForms A x J t 0 ≤ θ.toAddMonoidHom.ker := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      rw [SetLike.mem_coe, AddMonoidHom.mem_ker]
      show θ (c • ExteriorAlgebra.ιMulti K 0 v) = 0
      rw [map_smul, ExteriorAlgebra.ιMulti_zero_apply, hθ.1, smul_zero]
    exact key hη
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicUnitCarryingFormToNormMultiple
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem adelic_norm_move : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.C) (M : Type) [Field M] [NumberField M] (j : M →+* G.C) (σ : M →+* M), (∀ y : M, β * sh G (j y) = j (σ y) * β) → ∀ (a : M) (u : (AfP p ⊗[ℚ] M)ˣ), (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a → ∃ U : (AfP p ⊗[ℚ] G.C)ˣ, (U : AfP p ⊗[ℚ] G.C) * inC G (AfP p) β * (starT G.star (AfP p) U).unop = inC G (AfP p) (j a * β) ∧ ∀ y : G.C, (∀ m : M, y * j m = j m * y) → inC G (AfP p) y * U = U * inC G (AfP p) y := by
  intro p _ G β M _ _ j σ hβ a u hu
  let J : AfP p ⊗[ℚ] M →ₐ[ℚ] AfP p ⊗[ℚ] G.C := Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) j.toRatAlgHom
  have hJ : ∀ (r : AfP p) (m : M), J (r ⊗ₜ m) = r ⊗ₜ j m := fun r m => rfl
  have key : ∀ w : AfP p ⊗[ℚ] M, inC G (AfP p) β * (starT G.star (AfP p) (J w)).unop =
      J (Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom w) * inC G (AfP p) β := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      have e2 : J (Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom (r ⊗ₜ m)) = r ⊗ₜ j (σ m) := rfl
      rw [hJ, e2, starT_tmul]
      show ((1 : AfP p) ⊗ₜ β) * (r ⊗ₜ (G.star (j m)).unop) = (r ⊗ₜ j (σ m)) * ((1 : AfP p) ⊗ₜ β)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      congr 1
      exact hβ m
    | add x y hx hy => rw [map_add, map_add, map_add, MulOpposite.unop_add, mul_add, hx, hy, map_add, add_mul]
  refine ⟨Units.map J.toMonoidHom u, ?_, ?_⟩
  · show J u * inC G (AfP p) β * (starT G.star (AfP p) (J u)).unop = _
    rw [mul_assoc, key, ← mul_assoc, ← map_mul, hu, hJ]
    show ((1 : AfP p) ⊗ₜ j a) * ((1 : AfP p) ⊗ₜ β) = (1 : AfP p) ⊗ₜ (j a * β)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · intro y hy
    show inC G (AfP p) y * J u = J u * inC G (AfP p) y
    generalize (u : AfP p ⊗[ℚ] M) = w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hJ]
      show ((1 : AfP p) ⊗ₜ y) * (r ⊗ₜ j m) = (r ⊗ₜ j m) * ((1 : AfP p) ⊗ₜ y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hy m]
    | add x z hx hz => rw [map_add, mul_add, add_mul, hx, hz]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtalePullbackCoordinatesGoodCover
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverDeg

theorem etale_morphismRestrict_of_goodCover {k : Type} [CommRing k] {X Y : Scheme.{0}}
    (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (U : X.Opens) (hG : GoodCover p π D δ U) :
    Etale (π ∣_ U) := by
  obtain ⟨hU, hπU, -, hét, -⟩ := hG
  haveI : IsAffine U := hU
  haveI : IsAffine (π ⁻¹ᵁ U) := hπU
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    morphismRestrict_appLE]
  refine (Scheme.Hom.appLE_congr π _ (Scheme.Opens.ι_image_top U) (V' := π ⁻¹ᵁ U) ?_
    (fun φ => RingHom.Etale φ.hom)).2 ?_
  · rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top]
  · rw [← Scheme.Hom.app_eq_appLE]; exact hét

theorem etale_map_basicOpen {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W))
    (O : X.Opens) (hO : O = X.basicOpen g) (hle : O ≤ W) :
    (X.presheaf.map (homOfLE hle).op).hom.Etale := by
  subst hO
  have := hW.isLocalization_basicOpen g
  exact Algebra.Etale.of_isLocalizationAway g

theorem algX_comp {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X)
    (W : X.Opens) (V : Y.Opens) (h : V ≤ π ⁻¹ᵁ W) :
    ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (π ≫ p) V =
      (π.appLE W V h).hom.comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) := by
  have e : (π ≫ p).appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top _).ge) =
      p.appLE ⊤ W (le_top.trans (Scheme.Hom.preimage_top _).ge) ≫ π.appLE W V h := by
    first
      | rw [Scheme.Hom.appLE_comp_appLE]
      | (rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE])
      | (simp only [Scheme.Hom.comp_appLE, Scheme.Hom.appLE, Category.assoc, Scheme.Hom.naturality_assoc]; rfl)
  ext r
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, RingHom.comp_apply]
  rw [e, CommRingCat.comp_apply]

theorem etale_pullback_coords : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (D δ : ℕ) (U : X.Opens), GlobalTheory.CoverDeg.GoodCover p π D δ U → ∀ (W : X.Opens) (x : Fin D → Γ(X, W)), IsAffineOpen W → (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x).Etale → ∀ z : Y, π z ∈ U → π z ∈ W → ∃ V : Y.Opens, IsAffineOpen V ∧ z ∈ V ∧ ∃ h : V ≤ π ⁻¹ᵁ W, (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V) (fun a => (π.appLE W V h).hom (x a))).Etale := by
  intro k _ X Y p q π hπ D δ U hG W x hW hx z hzU hzW
  subst hπ
  have hE := etale_morphismRestrict_of_goodCover p π D δ U hG
  obtain ⟨hU, hπU, -⟩ := hG
  obtain ⟨f, g, hfg, hz⟩ := exists_basicOpen_le_affine_inter hU hW (π z) ⟨hzU, hzW⟩
  have hW'U : X.basicOpen f ≤ U := X.basicOpen_le f
  have hW'W : X.basicOpen f ≤ W := hfg ▸ X.basicOpen_le g
  have hW' : IsAffineOpen (X.basicOpen f) := hU.basicOpen f
  have hV : IsAffineOpen (π ⁻¹ᵁ X.basicOpen f) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact hπU.basicOpen _
  have hVU : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ U := fun y hy => hW'U hy
  have h : π ⁻¹ᵁ X.basicOpen f ≤ π ⁻¹ᵁ W := fun y hy => hW'W hy
  refine ⟨π ⁻¹ᵁ X.basicOpen f, hV, hz, h, ?_⟩

  have e1 : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (π ≫ p) (π ⁻¹ᵁ X.basicOpen f))
      (fun a => (π.appLE W _ h).hom (x a)) =
      (π.appLE W _ h).hom.comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x) := by
    rw [MvPolynomial.comp_eval₂Hom, algX_comp p π W _ h]
  rw [e1]
  refine RingHom.Etale.stableUnderComposition _ _ hx ?_

  have e2 : π.appLE W (π ⁻¹ᵁ X.basicOpen f) h =
      X.presheaf.map (homOfLE hW'W).op ≫ π.appLE (X.basicOpen f) (π ⁻¹ᵁ X.basicOpen f) le_rfl := by
    rw [Scheme.Hom.map_appLE]
  rw [e2, CommRingCat.hom_comp]
  refine RingHom.Etale.stableUnderComposition _ _ (etale_map_basicOpen hW g _ hfg hW'W) ?_

  have ha : IsAffineOpen (U.ι ⁻¹ᵁ X.basicOpen f) :=
    hW'.preimage_of_isOpenImmersion U.ι (by rw [Scheme.Opens.opensRange_ι]; exact hW'U)
  have hb : IsAffineOpen ((π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f)) :=
    hV.preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact hVU)
  have e3 : (π ⁻¹ᵁ U).ι ⁻¹ᵁ (π ⁻¹ᵁ X.basicOpen f) ≤ (π ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ X.basicOpen f) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
  have := HasRingHomProperty.appLE @Etale (π ∣_ U) hE ⟨_, ha⟩ ⟨_, hb⟩ e3
  rw [morphismRestrict_appLE] at this
  refine (Scheme.Hom.appLE_congr π _ ?_ ?_ (fun φ => RingHom.Etale φ.hom)).1 this
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hW'U
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hVU

end GlobalTheory.CoverDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeTrivialLocusRigidifiedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closed_subscheme_trivial_locus_rigidified : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ Sp R), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  first | exact @GlobalTheory.AffineTrivLocus.exists_closed_triv | exact GlobalTheory.AffineTrivLocus.exists_closed_triv | (intros; apply GlobalTheory.AffineTrivLocus.exists_closed_triv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeValuationEqDiscriminantStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cube_valuation_eq_discriminant : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ, ∃ A ∈ F, A ≠ 0 ∧ V.valuation A ^ 3 = V.valuation (latticeCurve L).Δ := by
  first | exact @GlobalTheory.CMModel.exists_mem_valuation_cube_eq_Δ | exact GlobalTheory.CMModel.exists_mem_valuation_cube_eq_Δ | (intros; apply GlobalTheory.CMModel.exists_mem_valuation_cube_eq_Δ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicGroupLawSplitByIdempotentStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logarithmic_group_law_split_by_idempotent : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d d' : ℕ) (G : LogFGL v d) (I : Matrix (Fin d) (Fin d') C) (P : Matrix (Fin d') (Fin d) C), (∀ a b, IsIntV v (I a b)) → (∀ a b, IsIntV v (P a b)) → P * I = 1 → (∃ φ, IsIntHom G G φ (I * P)) → (∃ ψ, IsIntHom G G ψ (1 - I * P)) → ∃ G' : LogFGL v d', (∃ j, IsIntHom G' G j I) ∧ ∃ q, IsIntHom G G' q P := by
  first | exact @GlobalTheory.IdemImage.exists_image | exact GlobalTheory.IdemImage.exists_image | (intros; apply GlobalTheory.IdemImage.exists_image <;> assumption)
end

