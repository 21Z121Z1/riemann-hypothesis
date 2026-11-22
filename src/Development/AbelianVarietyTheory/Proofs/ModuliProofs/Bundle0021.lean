import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.EtaleFamily

theorem analyticAt_eval₂Hom {E R J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CommRing R]
    (φ : E → (R →+* ℂ)) (u : E → J → ℂ) (w : E) (hφ : ∀ a, AnalyticAt ℂ (fun z => φ z a) w)
    (hu : ∀ i, AnalyticAt ℂ (fun z => u z i) w) (q : MvPolynomial J R) :
    AnalyticAt ℂ (fun z => MvPolynomial.eval₂Hom (φ z) (u z) q) w := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.eval₂Hom_C] using hφ a
  | add P Q hP hQ => simp only [map_add]; exact hP.add hQ
  | mul_X P i hP =>
    simp only [map_mul, MvPolynomial.eval₂Hom_X']
    exact hP.mul (hu i)

theorem hasDerivAt_eval₂Hom_line {R J : Type*} [CommRing R] [Fintype J]
    (φ : R →+* ℂ) (q : MvPolynomial J R) (y v : J → ℂ) :
    HasDerivAt (fun t : ℂ => MvPolynomial.eval₂Hom φ (y + t • v) q)
      (∑ i, MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv i q) * v i) 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : ℂ) (φ a)
  | add P Q hP hQ =>
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    exact hP.add hQ
  | mul_X P i hP =>
    have hX : HasDerivAt (fun t : ℂ => y i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add (y i)
    have h := hP.mul hX
    simp only [map_mul, MvPolynomial.eval₂Hom_X', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine HasDerivAt.congr_deriv h ?_
    have h1 : ∀ j, MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv j (P * MvPolynomial.X i)) * v j =
        MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv j P) * v j * y i +
        if i = j then MvPolynomial.eval₂Hom φ y P * v j else 0 := by
      intro j
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [hij, Pi.single_eq_of_ne hij]; ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.sum_mul]
    simp

theorem exists_local_inverse {E S J σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [CommRing S] [Fintype J] [Fintype σ] [DecidableEq σ]
    (χ : E → (S →+* ℂ)) (rel : σ → MvPolynomial J S) (c : σ → J) (hc : Function.Bijective c)
    (z₀ : E) (u₀ : J → ℂ) (hχ : ∀ a, AnalyticAt ℂ (fun z => χ z a) z₀)
    (hdet : (Matrix.of fun s r : σ =>
      MvPolynomial.eval₂Hom (χ z₀) u₀ (MvPolynomial.pderiv (c s) (rel r))).det ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph (E × (J → ℂ)) (E × (σ → ℂ)),
      (∀ w, Φ w = (w.1, fun r => MvPolynomial.eval₂Hom (χ w.1) w.2 (rel r))) ∧
      (z₀, u₀) ∈ Φ.source ∧ AnalyticOnNhd ℂ Φ.symm Φ.target := by
  first
  | exact @_root_.GlobalTheory.AnalyticLineDerivative.main
  | exact _root_.GlobalTheory.AnalyticLineDerivative.main
  | (apply _root_.GlobalTheory.AnalyticLineDerivative.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AnalyticLineDerivative.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AnalyticLineDerivative.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AnalyticLineDerivative.main ..)

theorem exists_holomorphic_sections :
    ∀ (m g : ℕ) (A R : Type) [CommRing A] [CommRing R] (ψ : MvPolynomial (Fin g) A →+* R) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (b₀ : Fin m → ℂ) (e : R →+* ℂ), ψ.Etale → IsOpen B → b₀ ∈ B → (∀ a, DifferentiableOn ℂ (fun b => φ b a) B) → (∀ a, e (ψ (MvPolynomial.C a)) = φ b₀ a) → ∃ (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (R →+* ℂ)) (n : ℕ) (f : Fin n → R) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))), IsOpen N ∧ IsOpen O ∧ (b₀, fun j => e (f j)) ∈ O ∧ (∀ a, DifferentiableOn ℂ (fun q => σ q a) N) ∧ (∀ q ∈ N, q.1 ∈ B ∧ (∀ a, σ q (ψ (MvPolynomial.C a)) = φ q.1 a) ∧ ∀ i, σ q (ψ (MvPolynomial.X i)) = q.2 i) ∧ ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) → (b, fun j => x (f j)) ∈ O → (b, fun i => x (ψ (MvPolynomial.X i))) ∈ N ∧ σ (b, fun i => x (ψ (MvPolynomial.X i))) = x := by
  intro m g A R _ _ ψ B φ b₀ e hψ hB hb₀ hφ he
  classical
  letI : Algebra (MvPolynomial (Fin g) A) R := ψ.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) A) R := hψ
  obtain ⟨J, τ, _, _, P, hP⟩ := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1
    ‹Algebra.Etale (MvPolynomial (Fin g) A) R›).out
  letI := Fintype.ofFinite J
  letI := Fintype.ofFinite τ
  have hcard : Fintype.card τ = Fintype.card J := by
    have := P.card_relations_le_card_vars_of_isFinite
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] at this hP
    omega
  have hbij : Function.Bijective P.map :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨P.map_inj, hcard⟩
  let π : MvPolynomial J (MvPolynomial (Fin g) A) →+* R := MvPolynomial.eval₂Hom ψ P.val
  have hπeq : ∀ a, π a = MvPolynomial.aeval P.val a := fun a => rfl
  have hπ : Function.Surjective π := P.aeval_val_surjective
  let χ : (Fin m → ℂ) × (Fin g → ℂ) → (MvPolynomial (Fin g) A →+* ℂ) :=
    fun q => MvPolynomial.eval₂Hom (φ q.1) q.2
  have hχ : ∀ q : (Fin m → ℂ) × (Fin g → ℂ), q.1 ∈ B → ∀ a, AnalyticAt ℂ (fun z => χ z a) q := by
    intro q hq a
    refine analyticAt_eval₂Hom (fun z : (Fin m → ℂ) × (Fin g → ℂ) => φ z.1) (fun z => z.2) q
      (fun c => ?_) (fun i => ?_) a
    · exact AnalyticAt.comp (g := fun b => φ b c) (f := fun w : (Fin m → ℂ) × (Fin g → ℂ) => w.1)
        (GlobalTheory.SCV.analyticAt_of_differentiableOn (hφ c) (hB.mem_nhds hq)) analyticAt_fst
    · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) i).comp
        (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin g → ℂ))).analyticAt _
  have hevj : ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) →
      MvPolynomial.eval₂Hom (χ (b, fun i => x (ψ (MvPolynomial.X i)))) (fun i => x (P.val i))
        = x.comp π := by
    intro b x hx
    refine MvPolynomial.ringHom_ext' ?_ ?_
    · refine MvPolynomial.ringHom_ext ?_ ?_
      · intro a; simp [χ, π, hx]
      · intro a; simp [χ, π]
    · intro i; simp [π]
  have hker : ∀ a, π a = 0 ↔ a ∈ Ideal.span (Set.range P.relation) := by
    intro a
    rw [P.span_range_relation_eq_ker]
    rw [P.ker_eq_ker_aeval_val]
    rfl
  obtain ⟨Φ, hΦ, hpS, hsymm⟩ := exists_local_inverse χ P.relation P.map hbij
    (b₀, fun i => e (ψ (MvPolynomial.X i))) (fun i => e (P.val i)) (hχ _ hb₀) (by
      rw [hevj b₀ e he]
      have h1 := (P.jacobian_isUnit.map e).ne_zero
      rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply, ← hπeq] at h1
      have h2 := (e.comp π).map_det P.jacobiMatrix
      have h3 : (e.comp π).mapMatrix P.jacobiMatrix = Matrix.of fun s r : τ =>
          (e.comp π) (MvPolynomial.pderiv (P.map s) (P.relation r)) := by
        ext s r
        simp [P.jacobiMatrix_apply]
      rw [← h3, ← h2]
      exact h1)
  have hfst : ∀ q, (q, 0) ∈ Φ.target → (Φ.symm (q, 0)).1 = q := by
    intro q hq
    have := Φ.right_inv hq
    rw [hΦ] at this
    exact congrArg Prod.fst this
  have hex : ∀ q : (Fin m → ℂ) × (Fin g → ℂ), ∃ x : R →+* ℂ, (q, 0) ∈ Φ.target →
      x.comp π = MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2 := by
    intro q
    by_cases hq : (q, 0) ∈ Φ.target
    · have hle : RingHom.ker π ≤
          RingHom.ker (MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2) := by
        intro a ha
        have : Ideal.span (Set.range P.relation) ≤
            RingHom.ker (MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2) := by
          rw [Ideal.span_le]
          rintro _ ⟨r, rfl⟩
          have h1 := Φ.right_inv hq
          rw [hΦ, hfst q hq] at h1
          exact congrFun (congrArg Prod.snd h1) r
        exact this ((hker a).1 ha)
      exact ⟨π.liftOfSurjective hπ ⟨_, hle⟩, fun _ => RingHom.ext fun c =>
        RingHom.liftOfRightInverse_comp_apply π _ (Function.rightInverse_surjInv hπ) ⟨_, hle⟩ c⟩
    · exact ⟨e, fun h => absurd h hq⟩
  choose s hs using hex
  let eqv := (Fintype.equivFin (Fin g ⊕ J))
  let κ : (Fin m → ℂ) × (Fin (Fintype.card (Fin g ⊕ J)) → ℂ) →
      ((Fin m → ℂ) × (Fin g → ℂ)) × (J → ℂ) :=
    fun y => ((y.1, fun i => y.2 (eqv (Sum.inl i))), fun i => y.2 (eqv (Sum.inr i)))
  have hκ : Continuous κ := by fun_prop
  let f : Fin (Fintype.card (Fin g ⊕ J)) → R :=
    fun j => Sum.elim (fun i => ψ (MvPolynomial.X i)) P.val (eqv.symm j)
  have hκf : ∀ (b : Fin m → ℂ) (x : R →+* ℂ), κ (b, fun j => x (f j)) =
      ((b, fun i => x (ψ (MvPolynomial.X i))), fun i => x (P.val i)) := by
    intro b x
    simp [κ, f]
  have hNo : IsOpen {q : (Fin m → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ (q, 0) ∈ Φ.target} :=
    (hB.preimage continuous_fst).inter
      (Φ.open_target.preimage (continuous_id.prodMk continuous_const))
  refine ⟨{q | q.1 ∈ B ∧ (q, 0) ∈ Φ.target}, s, _, f, {y | y.1 ∈ B ∧ κ y ∈ Φ.source}, hNo,
    (hB.preimage continuous_fst).inter (Φ.open_source.preimage hκ), ⟨hb₀, ?_⟩, ?_, ?_, ?_⟩
  · rw [hκf]; exact hpS
  · intro a
    obtain ⟨c, rfl⟩ := hπ a
    refine DifferentiableOn.congr
      (f := fun q => MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2 c) ?_ ?_
    · intro q hq
      refine (AnalyticAt.differentiableAt ?_).differentiableWithinAt
      have h1 : AnalyticAt ℂ (fun z : (Fin m → ℂ) × (Fin g → ℂ) => Φ.symm (z, 0)) q :=
        AnalyticAt.comp (f := fun z : (Fin m → ℂ) × (Fin g → ℂ) => (z, (0 : τ → ℂ)))
          (hsymm _ hq.2) (analyticAt_id.prod analyticAt_const)
      refine analyticAt_eval₂Hom χ (fun z => (Φ.symm (z, 0)).2) q (hχ q hq.1) (fun i => ?_) c
      exact AnalyticAt.comp (f := fun z : (Fin m → ℂ) × (Fin g → ℂ) => Φ.symm (z, 0))
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) i).comp
        (ContinuousLinearMap.snd ℂ ((Fin m → ℂ) × (Fin g → ℂ)) (J → ℂ))).analyticAt _) h1
    · intro q hq
      exact DFunLike.congr_fun (hs q hq.2) c
  · intro q hq
    refine ⟨hq.1, fun a => ?_, fun i => ?_⟩
    · simpa [π, χ] using DFunLike.congr_fun (hs q hq.2) (MvPolynomial.C (MvPolynomial.C a))
    · simpa [π, χ] using DFunLike.congr_fun (hs q hq.2) (MvPolynomial.C (MvPolynomial.X i))
  · rintro b x hx ⟨hb, hO⟩
    rw [hκf] at hO
    have hΦx : Φ ((b, fun i => x (ψ (MvPolynomial.X i))), fun i => x (P.val i)) =
        ((b, fun i => x (ψ (MvPolynomial.X i))), 0) := by
      rw [hΦ]
      refine Prod.ext rfl (funext fun r => ?_)
      change MvPolynomial.eval₂Hom (χ (b, fun i => x (ψ (MvPolynomial.X i))))
        (fun i => x (P.val i)) (P.relation r) = 0
      rw [hevj b x hx, RingHom.comp_apply, (hker _).2 (Ideal.subset_span ⟨r, rfl⟩), map_zero]
    have ht := Φ.map_source hO
    rw [hΦx] at ht
    refine ⟨⟨hb, ht⟩, ?_⟩
    have h1 := hs _ ht
    rw [← hΦx, Φ.left_inv hO, hevj b x hx] at h1
    ext a
    obtain ⟨c, rfl⟩ := hπ a
    exact DFunLike.congr_fun h1 c

end GlobalTheory.EtaleFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.UnifLieBasis

open TangentOrigin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR jetAug qD rD scaleD IsTan isTan_iff prodPts isLieComb_iff)

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem spMap_jetAug_surjective :
    Function.Surjective (spMap (jetAug ℂ (Fin 2) 1).toRingHom) := by
  intro q
  have : q ∈ Set.range (PrimeSpectrum.comap (jetAug ℂ (Fin 2) 1).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨algebraMap ℂ _ a, (jetAug ℂ (Fin 2) 1).commutes a⟩)]
    intro b hb
    refine q.2.mem_of_pow_mem (1 + 1) ?_
    have h := Ideal.pow_mem_pow (I := RingHom.ker (jetAug ℂ (Fin 2) 1)) hb (1 + 1)
    rw [Chart.ker_jetAug_pow, Ideal.mem_bot] at h
    rw [h]
    exact zero_mem _
  exact this

omit u in

theorem snd_evalPt_mul {v v' : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v) (hv' : IsTan (R := ℂ) (G := A) v')
    (U : A.left.Opens) (h0 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) (h' : ⊤ ≤ v'.left ⁻¹ᵁ U) (h'' : ⊤ ≤ (v * v').left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    (evalPt (R := DualNumber ℂ) (v * v').left U h'' f).snd =
      (evalPt (R := DualNumber ℂ) v.left U h f).snd + (evalPt (R := DualNumber ℂ) v'.left U h' f).snd := by
  let P : Chart.sp (R₀ := ℂ) (JetR ℂ (Fin 2) 1) ⟶ A := (Chart.spMap (qD 0) ≫ v) * (Chart.spMap (qD 1) ≫ v')
  have hP : Chart.spMap (jetAug ℂ (Fin 2) 1) ≫ P = 1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.jetAug_comp_qD, Chart.jetAug_comp_qD, hv, hv', _root_.mul_one]
  have hPU : ⊤ ≤ P.left ⁻¹ᵁ U := fun p _ => by
    obtain ⟨q, rfl⟩ := spMap_jetAug_surjective p
    rw [← hP] at h0
    exact h0 (Set.mem_univ q)
  have hval : ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ, Chart.spMap (rD l) ≫ P =
      (Chart.spMap (scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ v) * (Chart.spMap (scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ v') := by
    intro l
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Chart.spMap_comp, Chart.spMap_comp,
      Chart.restrictDiag_comp_incl_fst, Chart.restrictDiag_comp_incl_snd]
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), Chart.spMap (rD l) ≫ P = w →
      evalPt (R := DualNumber ℂ) w.left U hw f = rD l (evalPt (R := JetR ℂ (Fin 2) 1) P.left U hPU f) := by
    rintro l w hw rfl
    exact evalPt_spMap_comp (rD l : JetR ℂ (Fin 2) 1 →+* DualNumber ℂ) P.left U hPU hw f
  rw [key (LinearMap.fst ℂ ℂ ℂ) v h, key (LinearMap.snd ℂ ℂ ℂ) v' h',
    key (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) (v * v') h'', Chart.snd_rD_add]
  · rw [hval]
    simp only [LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply, add_zero, zero_add]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Category.id_comp]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv, _root_.one_mul]
  · rw [hval]
    simp only [LinearMap.fst_apply, LinearMap.snd_apply]
    rw [Chart.scaleD_one, Chart.spMap_id, Category.id_comp, Chart.spMap_scaleD_zero hv', _root_.mul_one]

theorem isDiff_add {w w' : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v)
    (hv' : IsTan (R := ℂ) (G := A) v') (hd : u.IsDiff w v) (hd' : u.IsDiff w' v') : u.IsDiff (w + w') (v * v') := by
  intro U h'' f
  have ht := Chart.isTan_mul hv hv'
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 ht) U).1 h''
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  have h' := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv') U).2 h0
  have h1 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by
    rw [← hv]
    exact fun p _ => h (Set.mem_univ _)
  rw [map_add, ← hd U h f, ← hd' U h' f]
  exact snd_evalPt_mul hv hv' U h1 h h' h'' f

theorem isDiff_smul {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (hv : IsTan (R := ℂ) (G := A) v) (hd : u.IsDiff w v) (c : ℂ) :
    u.IsDiff (c • w) (Chart.spMap (scaleD c) ≫ v) := by
  intro U h' f
  have h0 := (tangent_mem_iff (u := u) ((isTan_iff _).1 (Chart.isTan_scale c hv)) U).1 h'
  have h := (tangent_mem_iff (u := u) ((isTan_iff _).1 hv) U).2 h0
  rw [map_smul, ← hd U h f]
  refine (congrArg TrivSqZeroExt.snd
    (evalPt_spMap_comp (scaleD c : DualNumber ℂ →+* DualNumber ℂ) v.left U h h' f)).trans ?_
  exact TrivSqZeroExt.snd_map _ _

theorem isDiff_zero : u.IsDiff 0 (1 : epsR ℂ ⟶ A) := by
  intro U h f
  have ht : IsTan (R := ℂ) (G := A) (1 : epsR ℂ ⟶ A) := Chart.isTan_one
  have h1 : ⊤ ≤ (1 : Chart.sp (R₀ := ℂ) ℂ ⟶ A).left ⁻¹ᵁ U := by
    rw [← ht]
    exact fun p _ => h (Set.mem_univ _)
  have key : ∀ (w : epsR ℂ ⟶ A) (hw : ⊤ ≤ w.left ⁻¹ᵁ U), w = 1 →
      (evalPt (R := DualNumber ℂ) w.left U hw f).snd = (evalPt (R := DualNumber ℂ) (1 : epsR ℂ ⟶ A).left U h f).snd := by
    rintro w hw rfl
    rfl
  have h2 : ⊤ ≤ (1 * 1 : epsR ℂ ⟶ A).left ⁻¹ᵁ U := by rwa [_root_.mul_one]
  have := snd_evalPt_mul ht ht U h1 h h h2 f
  rw [key _ h2 (_root_.mul_one _)] at this
  rw [map_zero]
  exact left_eq_add.1 this

theorem isDiff_list_prod : ∀ {k : ℕ} (w : Fin k → Fin g → ℂ) (v : Fin k → (epsR ℂ ⟶ A)),
    (∀ i, IsTan (R := ℂ) (G := A) (v i)) → (∀ i, u.IsDiff (w i) (v i)) →
    IsTan (R := ℂ) (G := A) (List.ofFn v).prod ∧ u.IsDiff (∑ i, w i) (List.ofFn v).prod
  | 0, w, v, _, _ => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨Chart.isTan_one, isDiff_zero u⟩
  | k + 1, w, v, hv, hd => by
    obtain ⟨h1, h2⟩ := isDiff_list_prod (fun i => w i.succ) (fun i => v i.succ) (fun i => hv _) (fun i => hd _)
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact ⟨Chart.isTan_mul (hv 0) h1, isDiff_add u (hv 0) h1 (hd 0) h2⟩

theorem isTangent_comp (f : A ⟶ A) [IsMonHom f] {v : epsR ℂ ⟶ A} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem isDiff_comp (f : A ⟶ A) [IsMonHom f] (F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hd : u.IsDiff w v) : u.IsDiff (F w) (v ≫ f) := by
  intro U h s
  have h1 := hd (f.left ⁻¹ᵁ U) h ((f.left.app U).hom s)
  have e : ((v ≫ f).left.appLE U ⊤ h).hom s =
      (v.left.appLE (f.left ⁻¹ᵁ U) ⊤ h).hom ((f.left.app U).hom s) := by
    have := Scheme.Hom.comp_appLE v.left f.left U ⊤ h
    exact congrArg (fun φ => φ.hom s) this
  have hdiff := differentiableAt_val u ((tangent_mem_iff (u := u) (isTangent_comp f hv) U).1 h) s
  have hfun : (fun z => valAt' (u.ex z).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)) =
      (fun z => valAt' (u.ex z).left U s) ∘ F := by
    funext z
    rw [valAt'_comp, Function.comp_apply, hF]
    rfl
  have hch := (HasFDerivAt.comp (0 : Fin g → ℂ) (f := F)
    (by rw [map_zero]; exact hdiff.hasFDerivAt) F.hasFDerivAt).fderiv
  rw [hfun, hch] at h1
  rw [e]
  exact h1

end GlobalTheory.UnifLieBasis

open GlobalTheory.UnifLieBasis in
open ReciprocityTheory.ChartRestriction.G.Chart (IsTan isTan_iff prodPts isLieComb_iff isTan_scale) in

theorem GlobalTheory.exists_lieBasis_of_holUnif : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), Smooth A.hom → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → ∃ v : Fin g → (epsR ℂ ⟶ A), IsLieBasis v ∧ ∀ (f : A ⟶ A) (c : Fin g → ℂ), IsMonHom f → (∀ z, u.ex (fun k => c k * z k) = u.ex z ≫ f) → ∀ i, (v i ≫ f).left = spMap (epsScale (c i)) ≫ (v i).left := by
  intro A _ L g u _ h1 h2
  choose v hv using fun i : Fin g => (h2 (Pi.single i 1)).exists
  have ht : ∀ i, IsTan (R := ℂ) (G := A) (v i) := fun i => (isTan_iff _).2 (hv i).1
  have hp : ∀ c : Fin g → ℂ, IsTangent (prodPts (R := ℂ) (G := A) c v) ∧ u.IsDiff c (prodPts (R := ℂ) (G := A) c v) := by
    intro c
    obtain ⟨a, b⟩ := isDiff_list_prod u (fun i => c i • (Pi.single i 1 : Fin g → ℂ)) _
      (fun i => isTan_scale (c i) (ht i)) (fun i => isDiff_smul u (ht i) (hv i).2 (c i))
    rw [← pi_eq_sum_univ' c] at b
    exact ⟨(isTan_iff _).1 a, b⟩
  refine ⟨v, ⟨fun i => (hv i).1, fun w hw => ?_⟩, fun f c hf hF i => ?_⟩
  · obtain ⟨c, hc, hcu⟩ := h1 w hw
    refine ⟨c, (isLieComb_iff c v w).2 ((h2 c).unique ⟨hw, hc⟩ (hp c)), fun c' hc' => hcu c' ?_⟩
    rw [(isLieComb_iff c' v w).1 hc']
    exact (hp c').2
  · let F : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := ContinuousLinearMap.pi fun k => c k • ContinuousLinearMap.proj k
    have hd := isDiff_comp u f F hF (hv i).1 (hv i).2
    have e : F (Pi.single i 1) = c i • (Pi.single i 1 : Fin g → ℂ) := by
      funext k
      by_cases hk : k = i <;> simp [F, hk]
    rw [e] at hd
    exact congrArg CommaMorphism.left ((h2 _).unique ⟨isTangent_comp f (hv i).1, hd⟩
      ⟨(isTan_iff _).1 (isTan_scale (c i) (ht i)), isDiff_smul u (ht i) (hv i).2 (c i)⟩)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LiePull

theorem exists_pushEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f) :
    ∃ e : (T ⟶ G') ≃* (Over.mk g ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  subst hg
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => ?_, fun y => ?_⟩, fun x => rfl⟩
  · have e' : x.left ≫ φ = y.left ≫ φ := congrArg (fun z => z.left) e
    exact Over.OverMorphism.ext (h.1.hom_ext e' ((Over.w x).trans (Over.w y).symm))
  · exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem basis_transport {A B k : Type} [Monoid A] [Monoid B] (e : A ≃* B) {P : A → Prop} {Q : B → Prop}
    {R : k → A → A → Prop} {R' : k → B → B → Prop} (hP : ∀ x, P x ↔ Q (e x))
    (hR : ∀ c x y, R c x y ↔ R' c (e x) (e y)) (n : ℕ)
    (H : ∃ v : Fin n → A, (∀ i, P (v i)) ∧ ∀ w, P w →
      ∃! c : Fin n → k, ∃ u : Fin n → A, (∀ i, R (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod) :
    ∃ v : Fin n → B, (∀ i, Q (v i)) ∧ ∀ w, Q w →
      ∃! c : Fin n → k, ∃ u : Fin n → B, (∀ i, R' (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod := by
  obtain ⟨v, hv, H⟩ := H
  refine ⟨fun i => e (v i), fun i => (hP _).1 (hv i), fun w hw => ?_⟩
  obtain ⟨w, rfl⟩ := e.surjective w
  have pr : ∀ u : Fin n → A, e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  refine (existsUnique_congr fun c => ⟨?_, ?_⟩).1 (H w ((hP _).2 hw))
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
    rw [pr, hw]
    simp

theorem lieMult_pull : ∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n := by
  intro O _ S S' G G' _ _ f φ a a' h hact k _ x τ n
  obtain ⟨e, he⟩ := exists_pushEquiv h (epsPt x) (spMap (algebraMap k (DualNumber k)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : ∀ c : k, spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) =
      spMap (algebraMap k (DualNumber k)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (c : k) (u v : epsPt x ⟶ G'), u.left = spMap (epsScale c) ≫ v.left ↔
      (e u).left = spMap (epsScale c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScale c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc c))
  have hP : ∀ v : epsPt x ⟶ G', IsLieEigen a' x τ v ↔ IsLieEigen a (x ≫ f) τ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
      refine (congrArg (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ ·) (Over.w v)).trans ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
    · have E : e (v ≫ a'.act c) = e v ≫ a.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
      rw [hR, E]
  constructor
  · exact basis_transport e (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left) hP hR n
  · exact basis_transport e.symm (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (fun v => by rw [hP, e.apply_symm_apply])
      (fun c u v => by rw [hR, e.apply_symm_apply, e.apply_symm_apply]) n

end GlobalTheory.LiePull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientExistsUniqueCompEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem quotient_existsUnique_comp_eq :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (T : Scheme.{0}) (f : X ⟶ T), (∀ g, (ρ g).hom ≫ f = f) → ∃! f' : X' ⟶ T, π ≫ f' = f := by
  intro Γ _ _ X X' ρ π ⟨hπ, hinv, hV⟩ T f hf

  have hq : IsAffineQuotient ρ π :=
    { comp_eq := hinv
      isAffineHom := hπ
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (fun g _ => by obtain ⟨_, e⟩ := hs g; exact e) }
  exact hq.existsUnique_comp_eq f hf

end GlobalTheory
end

