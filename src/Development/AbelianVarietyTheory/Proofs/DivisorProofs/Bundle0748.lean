import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0717
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationChartCoboundaryOnChartsFirstOrder
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartCobd

open GlobalTheory.CatCoh GlobalTheory.AnPer.Charts

theorem tsze_mul_of_fst {A : Type} [CommRing A] {n : ℕ} (x y : TrivSqZeroExt A (Fin n → A)) (hx : x.fst = 0)
    (hy : y.fst = 0) : x * y = 0 := by
  ext : 1 <;> simp [hx, hy]

theorem comap_fst_nil {A : Type} [CommRing A] {n : ℕ} (J : Ideal A) (hJ : IsNilpotent J) :
    IsNilpotent (J.comap (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom) := by
  obtain ⟨N, hN⟩ := hJ
  refine ⟨N * 2, ?_⟩
  have h1 : (J.comap (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom) ^ N ≤
      RingHom.ker (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom := by
    refine (Ideal.le_comap_pow _ N).trans ?_
    rw [hN, Ideal.zero_eq_bot]
    exact le_of_eq rfl
  rw [pow_mul, Ideal.zero_eq_bot, eq_bot_iff]
  refine (Ideal.pow_right_mono h1 2).trans ?_
  rw [pow_two, Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  exact tsze_mul_of_fst a b ha hb

section Gen

variable {R : Type} [CommRing R] [Algebra ℂ R] {O O' : Type} [CommRing O] [Algebra ℂ O] [CommRing O'] [Algebra ℂ O']

theorem map_alg (φ : O →ₐ[ℂ] O') (r : R) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ (algebraMap R (R ⊗[ℂ] O) r) = algebraMap R (R ⊗[ℂ] O') r := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem map_mem (φ : O →ₐ[ℂ] O') (M : Ideal R) (c : R ⊗[ℂ] O) (hc : c ∈ M.map (algebraMap R (R ⊗[ℂ] O))) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ c ∈ M.map (algebraMap R (R ⊗[ℂ] O')) := by
  have e : (Algebra.TensorProduct.map (AlgHom.id ℂ R) φ).toRingHom.comp (algebraMap R (R ⊗[ℂ] O)) =
      algebraMap R (R ⊗[ℂ] O') := RingHom.ext (map_alg φ)
  have := Ideal.mem_map_of_mem (Algebra.TensorProduct.map (AlgHom.id ℂ R) φ).toRingHom hc
  rwa [Ideal.map_map, e] at this

theorem map_right (φ : O →ₐ[ℂ] O') (x : O) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (φ x) := by
  simp

theorem map_nil {A : Type} [CommRing A] (f : R →+* A) (M : Ideal R) (h : IsNilpotent M) : IsNilpotent (M.map f) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by rw [← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]⟩

theorem lTensor_alg (D : Derivation ℂ O O) (r : R) :
    LinearMap.lTensor R D.toLinearMap (algebraMap R (R ⊗[ℂ] O) r) = 0 := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem lTensor_right (D : Derivation ℂ O O) (x : O) :
    LinearMap.lTensor R D.toLinearMap (Algebra.TensorProduct.includeRight (R := ℂ) (A := R) x) =
      Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (D x) := by
  simp

theorem right_alg (c : ℂ) : Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (algebraMap ℂ O c) =
    algebraMap R (R ⊗[ℂ] O) (algebraMap ℂ R c) := by
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem tensor_subsingleton [Subsingleton O] (x y : R ⊗[ℂ] O) : x = y := Subsingleton.elim _ _

theorem alg_tmul (r : R) : algebraMap R (R ⊗[ℂ] O) r = r ⊗ₜ[ℂ] 1 := rfl

theorem fst_inl_inr {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A) :
    (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)).fst = x := by simp

theorem eq_zero_of_inl_inr {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A)
    (h : (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)) = TrivSqZeroExt.inl x) : v = 0 := by
  simpa using congrArg TrivSqZeroExt.snd h

theorem inl_add_zero {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A) (h : ∀ a, v a = 0) :
    (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)) = TrivSqZeroExt.inl x := by
  rw [show v = 0 from funext h]; simp

end Gen

variable {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R]
  {et : Hol F₀.V →+* R} {M : Ideal R}

theorem right_cst (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) (k : K₀.K) (f : Hol F₀.V) :
    Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (K₀.cst k f) = algebraMap R (R ⊗[ℂ] Hol (K₀.W k)) (et f) := by
  by_cases hW : ∃ p, p ∈ K₀.W k
  · obtain ⟨p, hp⟩ := hW
    have e : K₀.cst k f = algebraMap ℂ (Hol (K₀.W k)) (f.fn p.1) := Hol.ext_fn fun p' hp' ↦ by
      rw [K₀.fn_cst k f hp', Hol.fn_algebraMap _ hp', Subsingleton.elim p'.1 p.1]
    rw [e, hev f p.1 (K₀.base k p hp)]
    exact right_alg _
  · haveI : Subsingleton (Hol (K₀.W k)) := ⟨fun a b ↦ Hol.ext_fn fun p hp ↦ (hW ⟨p, hp⟩).elim⟩
    exact tensor_subsingleton _ _

@[reducible] def objS (hM : IsNilpotent M) (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) (k : K₀.K) :
    K₀.DObj et M where
  T :=
    { k := k
      C := R ⊗[ℂ] Hol (K₀.W k)
      alg := ((algebraMap R (R ⊗[ℂ] Hol (K₀.W k))).comp et).toAlgebra
      J := M.map (algebraMap R (R ⊗[ℂ] Hol (K₀.W k)))
      nil := map_nil _ M hM
      ρ := (Algebra.TensorProduct.includeRight (R := ℂ) (A := R)).toRingHom
      ρ_cst := right_cst K₀ hev k }
  alg := Algebra.TensorProduct.leftAlgebra
  compat _ := rfl
  mem _ hd := Ideal.mem_map_of_mem _ hd

def homS (hM : IsNilpotent M) (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) {l : Λ} {k k' : K₀.K}
    (h : K₀.le l k' k) : objS K₀ hM hev k ⟶ objS K₀ hM hev k' :=
  ⟨{ φ := letI := (objS K₀ hM hev k).T.alg; letI := (objS K₀ hM hev k').T.alg
      { (Algebra.TensorProduct.map (AlgHom.id ℂ R) (shA h)).toRingHom with commutes' := fun f ↦ map_alg (shA h) (et f) }
     deg := l
     le := h
     mem := map_mem (shA h) M
     close := by
       have e : (Algebra.TensorProduct.map (AlgHom.id ℂ R) (shA h)).toRingHom.comp (objS K₀ hM hev k).T.ρ =
           (objS K₀ hM hev k').T.ρ.comp (sh h) := RingHom.ext fun x ↦ map_right (R := R) (shA h) x
       exact Eq.mpr (congrArg (Close _ _) e) Relation.ReflTransGen.refl },
   map_alg (shA h)⟩

variable {K₀}

@[reducible] def jetD (S : K₀.DObj et M) : K₀.DObj et M where
  T :=
    { k := S.T.k
      C := TrivSqZeroExt S.T.C (Fin g → S.T.C)
      alg := ((TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp (algebraMap (Hol F₀.V) S.T.C)).toAlgebra
      J := S.T.J.comap (TrivSqZeroExt.fstHom ℤ S.T.C (Fin g → S.T.C)).toRingHom
      nil := comap_fst_nil _ S.T.nil
      ρ := (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp S.T.ρ
      ρ_cst := fun f ↦ congrArg (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)) (S.T.ρ_cst f) }
  alg := ((TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp (algebraMap R S.T.C)).toAlgebra
  compat f := congrArg (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)) (S.compat f)
  mem d hd := S.mem d hd

def jetHom (S : K₀.DObj et M) (ψ : S.T.C →+* TrivSqZeroExt S.T.C (Fin g → S.T.C)) (D : S.T.C → Fin g → S.T.C)
    (hψ : ∀ x, ψ x = TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x)) (hR : ∀ r a, D (algebraMap R S.T.C r) a = 0)
    (hc : Close (jetD S).T.J (jetD S).T.ρ (ψ.comp S.T.ρ)) : S ⟶ jetD S :=
  ⟨{ φ := letI := (jetD S).T.alg
      { ψ with commutes' := fun f ↦ (hψ _).trans (inl_add_zero _ _ fun a ↦ by rw [S.compat]; exact hR _ a) }
     deg := 0
     le := K₀.le_refl _
     mem := fun c hc ↦ by
       change (ψ c).fst ∈ S.T.J
       rw [hψ, fst_inl_inr]; exact hc
     close := Eq.mpr (congrArg (fun ρ ↦ Close (jetD S).T.J ρ (ψ.comp S.T.ρ))
       (RingHom.ext fun x ↦ congrArg (jetD S).T.ρ (sh_refl (K₀.le_refl _) x))) hc },
   fun d ↦ (hψ _).trans (inl_add_zero _ _ (hR d))⟩

theorem killed {q : Λ →+ R} (s : ∀ S : K₀.DObj et M, S.T.C)
    (key : ∀ {S S' : K₀.DObj et M} (f : S ⟶ S'), s S' - f.1.φ (s S) = algebraMap R S'.T.C (q f.1.deg))
    (S : K₀.DObj et M) (ψ : S.T.C →+* TrivSqZeroExt S.T.C (Fin g → S.T.C)) (D : S.T.C → Fin g → S.T.C)
    (hψ : ∀ x, ψ x = TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x)) (hR : ∀ r a, D (algebraMap R S.T.C r) a = 0)
    (hD : ∀ h a, D (S.T.ρ h) a = S.T.ρ (dw a h)) : D (s S) = 0 := by
  have e0 := key (jetHom S (TrivSqZeroExt.inlHom _ _) (fun _ ↦ 0) (fun x ↦ (inl_add_zero x _ fun _ ↦ rfl).symm)
    (fun _ _ ↦ rfl) Relation.ReflTransGen.refl)
  have e1 := key (jetHom S ψ D hψ hR (Relation.ReflTransGen.single
    ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ S.T.J.zero_mem, fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _,
      fun h ↦ (hψ _).trans (by
        rw [show D (S.T.ρ h) = fun a ↦ S.T.ρ (dw a h) from funext (hD h)]
        exact tsze_expand _ _)⟩))
  have e2 : ψ (s S) = TrivSqZeroExt.inl (s S) := sub_right_injective (e1.trans e0.symm)
  exact eq_zero_of_inl_inr _ _ ((hψ _).symm.trans e2)

theorem coboundary_on_charts : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →+* R) (M : Ideal R), IsNilpotent M → (∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ (q : Λ →+ R), K₀.perClD et M q = 0 → ∃ G : ∀ k, R ⊗[ℂ] Hol (K₀.W k), (∀ k a, LinearMap.lTensor R (dw a).toLinearMap (G k) = 0) ∧ ∀ l k k' (h : K₀.le l k' k), G k' - Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h) (G k) = q l ⊗ₜ[ℂ] 1 := by
  intro g Λ _ F₀ K₀ R _ _ et M hM hev q hq
  obtain ⟨s, hs⟩ := CatCoh.H1.mk_eq_zero.1 hq
  have key : ∀ {S S' : K₀.DObj et M} (f : S ⟶ S'),
      @HSub.hSub S'.T.C S'.T.C S'.T.C _ (s S') (f.1.φ (s S)) = algebraMap R S'.T.C (q f.1.deg) :=
    fun f ↦ congrFun (congrFun (congrFun hs _) _) f
  refine ⟨fun k ↦ s (objS K₀ hM hev k), fun k a ↦ ?_, fun l k k' h ↦ key (homS K₀ hM hev h)⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.SqZeroMove.sqZeroMove (TrivSqZeroExt.inlHom (R ⊗[ℂ] Hol (K₀.W k)) (Fin g → R ⊗[ℂ] Hol (K₀.W k)))
    (fun a ↦ TrivSqZeroExt.inr (Pi.single a 1)) (fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _)
  exact congrFun (killed s key (objS K₀ hM hev k) ψ (fun x a ↦ LinearMap.lTensor R (dw a).toLinearMap x)
    (fun x ↦ (hψ x).trans (tsze_expand _ _).symm) (fun r a ↦ lTensor_alg _ r) (fun h a ↦ lTensor_right _ h)) a

end GlobalTheory.ChartCobd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRestrictionEq
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem uniformisedOneFormEvaluation_restriction_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V) (ξ : Ω[Sec (str A) U.1⁄ℂ]), ∀ z ∈ pre u.ex V.1, evForm u.ex V.1 z (p1 (OAff (str A)) a ξ) = evForm u.ex U.1 z ξ := by
  intro A _ g L u U V a ξ z hz
  obtain ⟨hopen, -, -, -, -, hmono, -, -, hres, -, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hVU : V.1 ≤ U.1 := leOfHom a.unop
  have hzU : z ∈ pre u.ex U.1 := hmono _ _ hVU hz
  have evV := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u V.1 z hz
  have evU := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hzU
  have hD : ∀ b : Sec (str A) U.1, fderiv ℂ (val u.ex V.1 (Sec.res (str A) hVU b)) z = fderiv ℂ (val u.ex U.1 b) z := by
    intro b
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(hopen V.1).mem_nhds hz] with w hw
    exact hres _ _ hVU b w hw
  have hξ : ξ ∈ Submodule.span (Sec (str A) U.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U.1))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [p1_D, evV.2.2, evU.2.2]
    exact hD b
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul b x _ hx =>
    rw [oneFormsMapOfFunctorMorphism_smul, evV.2.1, evU.2.1, hx]
    congr 1
    exact hres _ _ hVU b z hz

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesHasStrictFDerivAt
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem yF_hasStrictFDerivAt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : IsOrth X x) : HasStrictFDerivAt (yF X) (dY X) 0 := by
  obtain ⟨R, hR, hball⟩ := exists_ball X hx
  have hnhds : {w | cpt X x w ∈ X.dom} ∈ nhds (0 : V (nd X)) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hR) fun w hw => hball w hw
  have hB : ∀ τ k b, ContDiffAt ℝ ∞ (fun w => gsB X w τ k b) 0 := fun τ k b =>
    (GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor X hx τ k b).contDiffAt hnhds
  have hN : ∀ τ a k, ContDiffAt ℝ ∞ (fun w : V (nd X) => nmat X w τ a k) 0 := fun τ a k =>
    have h1 : ContDiff ℂ ∞ (fun w : V (nd X) => nmat X w τ a k) := by
      unfold nmat
      split_ifs
      · exact ((EuclideanSpace.proj _ : V (nd X) →L[ℂ] ℂ)).contDiff
      · exact contDiff_const
      · exact contDiff_const
    (h1.restrict_scalars ℝ).contDiffAt
  have hY : ContDiffAt ℝ ∞ (yF X) 0 := by
    rw [contDiffAt_pi]; intro τ
    rw [contDiffAt_pi]; intro a
    rw [contDiffAt_pi]; intro b
    show ContDiffAt ℝ ∞ (fun w => (mat (nmat X w) τ * gsB X w τ) a b) 0
    simp only [Matrix.mul_apply]
    refine ContDiffAt.sum fun k _ => ?_
    exact (hN τ a k).mul (hB τ k b)
  exact hY.hasStrictFDerivAt (by simp)

end GlobalTheory.SUChartSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittExtensionDiagonalGramTuples
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_etale_kill_of_indEt : ∀ (q : ℕ) (B O : Type) [CommRing B] [CommRing O] [Algebra B O], IsUnit (q : B) → IndEt B O → ∀ (n i : ℤ) (y : Ht q (sp B) n i), pull _ (spMap (algebraMap B O)) _ _ y = 0 → ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (_ : D →ₐ[B] O), pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  intro q B O _ _ _ hq hO n i y hy
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, het⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt B O hO
  have hc' : IsColimit ((Under.forget (CommRingCat.of B)).mapCocone (Cocone.mk _ ι)) :=
    isColimitOfPreserves (Under.forget _) hc
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  have hqj : IsUnit ((q : ((D ⋙ Under.forget _).obj j))) := by
    have := hq.map (D.obj j).hom.hom
    rw [map_natCast] at this
    exact this
  have hyj : pull _ (spMap ((Under.forget _).mapCocone (Cocone.mk _ ι) |>.ι.app j).hom) _ _
      (pull _ (spMap (D.obj j).hom.hom) _ _ y) = 0 := by
    erw [← pull_comp]
    have hw : (D.obj j).hom ≫ (ι.app j).right = CommRingCat.ofHom (algebraMap B O) := by
      simpa using Under.w (ι.app j)
    have : spMap ((Under.forget _).mapCocone (Cocone.mk _ ι) |>.ι.app j).hom ≫ spMap (D.obj j).hom.hom
        = spMap (algebraMap B O) := by
      simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
      congr 2 <;> simpa using hw
    erw [this]; exact hy
  obtain ⟨k, f, hk⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (D ⋙ Under.forget _) _ hc' n i).2 j _ hqj hyj
  erw [← pull_comp] at hk
  have hwk : (D.obj j).hom ≫ (D.map f).right = (D.obj k).hom := by simpa using Under.w (D.map f)
  letI : Algebra B (D.obj k).right := (D.obj k).hom.hom.toAlgebra
  refine ⟨(D.obj k).right, inferInstance, this, het k, ⟨(ι.app k).right.hom, fun b => ?_⟩, ?_⟩
  · have hw : (D.obj k).hom ≫ (ι.app k).right = CommRingCat.ofHom (algebraMap B O) := by
      simpa using Under.w (ι.app k)
    exact congrArg (fun g => g.hom b) hw
  · have : spMap ((D ⋙ Under.forget _).map f).hom ≫ spMap (D.obj j).hom.hom
        = spMap (algebraMap B (D.obj k).right) := by
      simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
      congr 2 <;> simpa using hwk
    erw [this] at hk; exact hk

end GlobalTheory.EtC
end

