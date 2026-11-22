import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0109
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.NeutralLocalFields.Bundle0001
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.TendstoUnderCofinite
import Formalism.ConjugateSelfDual.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqMulFinrankMatrixAlgebraHomEqFinrankMul
section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MatCount

open Matrix Module

variable {k : Type} [Field k] {n : ℕ}

section
variable {X : Type} [AddCommGroup X] [Module k X]
  (ρ : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k X)

theorem unit_mul (i j l p : Fin (n+1)) (x : X) :
    ρ (single i j 1) (ρ (single l p 1) x) = if j = l then ρ (single i p 1) x else 0 := by
  rw [← Module.End.mul_apply, ← map_mul]
  split_ifs with h
  · subst h; rw [single_mul_single_same, mul_one]
  · rw [single_mul_single_of_ne (h := h), map_zero, LinearMap.zero_apply]

theorem recon (x : X) : ∑ i, ρ (single i 0 1) (ρ (single 0 i 1) x) = x := by
  simp only [unit_mul, if_true]
  rw [← LinearMap.sum_apply, ← map_sum, sum_single_one, map_one, Module.End.one_apply]

abbrev corner : Submodule k X := LinearMap.range (ρ (single 0 0 1))

theorem unit_mem_corner (i : Fin (n+1)) (x : X) : ρ (single 0 i 1) x ∈ corner ρ :=
  ⟨ρ (single 0 i 1) x, by rw [unit_mul]; simp⟩

theorem unit_corner (v : corner ρ) (i : Fin (n+1)) :
    ρ (single 0 i 1) (v : X) = if i = 0 then (v : X) else 0 := by
  obtain ⟨y, hy⟩ := v.2
  rw [← hy, unit_mul]

def cut (i : Fin (n+1)) : X →ₗ[k] corner ρ :=
  (ρ (single 0 i 1)).codRestrict (corner ρ) (unit_mem_corner ρ i)

@[simp] theorem cut_coe (i : Fin (n+1)) (x : X) : ((cut ρ i x : corner ρ) : X) = ρ (single 0 i 1) x := rfl

theorem cut_unit (i l p : Fin (n+1)) (x : X) :
    cut ρ i (ρ (single l p 1) x) = if i = l then cut ρ p x else 0 := by
  apply Subtype.ext
  rw [cut_coe, unit_mul]
  split_ifs <;> simp

theorem cut_corner (i : Fin (n+1)) (v : corner ρ) : cut ρ i v = if i = 0 then v else 0 := by
  apply Subtype.ext
  rw [cut_coe, unit_corner]
  split_ifs <;> simp

def piEquiv : X ≃ₗ[k] (Fin (n+1) → corner ρ) :=
  LinearEquiv.ofLinear (LinearMap.pi fun i => cut ρ i)
    (∑ i, ρ (single i 0 1) ∘ₗ (corner ρ).subtype ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.ext fun v => funext fun j => ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
        Submodule.subtype_apply, LinearMap.proj_apply, cut_unit, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, cut_corner, LinearMap.id_apply])
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
        cut_coe, Submodule.subtype_apply, LinearMap.proj_apply, LinearMap.id_apply]
      exact recon ρ x)

theorem finrank_eq [FiniteDimensional k X] : finrank k X = (n+1) * finrank k (corner ρ) := by
  rw [(piEquiv ρ).finrank_eq, Module.finrank_pi_fintype]
  simp
end

section
variable {X Y : Type} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
  (ρX : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k X)
  (ρY : Matrix (Fin (n+1)) (Fin (n+1)) k →ₐ[k] Module.End k Y)

theorem comm {T : X →ₗ[k] Y} (hT : T ∈ GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) (a : Matrix (Fin (n+1)) (Fin (n+1)) k)
    (x : X) : T (ρX a x) = ρY a (T x) :=
  (GlobalTheory.HTRho.mem_homO _ _ T).1 hT a x

theorem maps_corner (T : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) :
    ∀ x ∈ corner ρX, (T : X →ₗ[k] Y) x ∈ corner ρY := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(T : X →ₗ[k] Y) y, (comm ρX ρY T.2 _ y).symm⟩

def restr : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom →ₗ[k] (corner ρX →ₗ[k] corner ρY) where
  toFun T := (T : X →ₗ[k] Y).restrict (maps_corner ρX ρY T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restr_coe (T : GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) (v : corner ρX) :
    ((restr ρX ρY T v : corner ρY) : Y) = (T : X →ₗ[k] Y) v := rfl

def ext (S : corner ρX →ₗ[k] corner ρY) : X →ₗ[k] Y :=
  ∑ i, ρY (single i 0 1) ∘ₗ (corner ρY).subtype ∘ₗ S ∘ₗ cut ρX i

theorem ext_apply (S : corner ρX →ₗ[k] corner ρY) (x : X) :
    ext ρX ρY S x = ∑ i, ρY (single i 0 1) (S (cut ρX i x)) := by
  simp [ext, LinearMap.sum_apply]

theorem ext_unit (S : corner ρX →ₗ[k] corner ρY) (l p : Fin (n+1)) (x : X) :
    ext ρX ρY S (ρX (single l p 1) x) = ρY (single l p 1) (ext ρX ρY S x) := by
  rw [ext_apply, ext_apply, map_sum]
  simp only [cut_unit, unit_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single l (fun b _ hb => by rw [if_neg hb, map_zero, Submodule.coe_zero, map_zero])
    (by simp)]
  simp

theorem ext_mem (S : corner ρX →ₗ[k] corner ρY) :
    ext ρX ρY S ∈ GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom := by
  rw [GlobalTheory.HTRho.mem_homO]
  intro a x
  change ext ρX ρY S (ρX a x) = ρY a (ext ρX ρY S x)
  have ha : a = ∑ l, ∑ p, a l p • single l p (1 : k) := by
    conv_lhs => rw [matrix_eq_sum_single a]
    simp only [smul_single, smul_eq_mul, mul_one]
  rw [ha]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, ext_unit]

theorem restr_bij : Function.Bijective (restr ρX ρY) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun T hT => ?_
    apply Subtype.ext
    refine LinearMap.ext fun x => ?_
    have h0 : ∀ i, (T : X →ₗ[k] Y) (ρX (single 0 i 1) x) = 0 := fun i => by
      exact (congrArg Subtype.val (LinearMap.congr_fun hT ⟨_, unit_mem_corner ρX i x⟩) :)
    change (T : X →ₗ[k] Y) x = 0
    rw [← recon ρX x, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [comm ρX ρY T.2, h0, map_zero]
  · intro S
    refine ⟨⟨ext ρX ρY S, ext_mem ρX ρY S⟩, LinearMap.ext fun v => Subtype.ext ?_⟩
    rw [restr_coe]
    change ext ρX ρY S v = _
    rw [ext_apply]
    simp only [cut_corner]
    rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [if_neg hb, map_zero, Submodule.coe_zero, map_zero])
      (by simp)]
    simp [unit_corner]

theorem finrank_homO [FiniteDimensional k X] [FiniteDimensional k Y] :
    finrank k (GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) = finrank k (corner ρX) * finrank k (corner ρY) := by
  rw [(LinearEquiv.ofBijective _ (restr_bij ρX ρY)).finrank_eq, Module.finrank_linearMap]
end

theorem count : ∀ (k : Type) [Field k] (m : ℕ) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (ρX : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k X) (ρY : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k Y),
    m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) = Module.finrank k X * Module.finrank k Y := by
  intro k _ m X Y _ _ _ _ _ _ ρX ρY
  cases m with
  | zero =>
    have hX : Subsingleton X := by
      refine ⟨fun a b => ?_⟩
      have h : (1 : Module.End k X) = 0 := by
        rw [← map_one ρX, ← map_zero ρX]
        congr 1
        ext i
        exact i.elim0
      have ha := congrArg (fun f : Module.End k X => f a) h
      have hb := congrArg (fun f : Module.End k X => f b) h
      simp only [Module.End.one_apply, LinearMap.zero_apply] at ha hb
      rw [ha, hb]
    simp [finrank_zero_of_subsingleton]
  | succ n =>
    rw [finrank_homO, finrank_eq ρX, finrank_eq ρY]
    ring

end GlobalTheory.MatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqScalarCharacterOfDoubleCoverUnitaryStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_scalar_character_of_double_cover_unitary : ∀ (G G' M H : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [Group M]
    [TopologicalSpace M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H] (pr : G' →* M) (s : G →* M)
    (om : G' →* (H ≃ₗᵢ[ℂ] H)) (ω : G →* (H ≃ₗᵢ[ℂ] H)) (ε : G'), IsCoveringMap pr → Function.Surjective pr →
    (∀ g, pr g = 1 → g = 1 ∨ g = ε) → (∀ v, om ε v = -v) → Continuous s → (∀ v, Continuous fun g => om g v) →
    (∀ v, Continuous fun g => ω g v) → (∀ g g', pr g' = s g → ∃ a : ℂ, ∀ v, ω g v = a • om g' v) →
    ∃ η : G → ℂ, (∀ g h, η (g * h) = η g * η h) ∧ Continuous η ∧ (∀ g, η g ≠ 0) ∧
      ∀ g g' (a : ℂ), pr g' = s g → (∀ v, ω g v = a • om g' v) → a ^ 2 = η g := by
  first | exact @GlobalTheory.sq_scalar_character | exact GlobalTheory.sq_scalar_character | (intros; apply GlobalTheory.sq_scalar_character <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroDeformationFactorsThroughLinearStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_zero_deformation_factors_through_linear : ∀ (R₀ B K : Type) [CommRing R₀] [CommRing B] [Algebra R₀ B] [Field K] (n : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension n R₀ B → ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ R : B →+* TrivSqZeroExt K (ι → K), (∀ a : R₀, R (algebraMap R₀ B a) = TrivSqZeroExt.inl (R (algebraMap R₀ B a)).fst) →
    (∀ M M' : ι → K, (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R =
      (TrivSqZeroExt.map (Fintype.linearCombination K M')).toRingHom.comp R → M = M') →
    ∀ g : B →+* DualNumber K, (∀ b, (g b).fst = (R b).fst) →
    (∀ a : R₀, g (algebraMap R₀ B a) = TrivSqZeroExt.inl (g (algebraMap R₀ B a)).fst) →
    ∃ M : ι → K, g = (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom.comp R := by
  first | exact @GlobalTheory.FirstOrderPoints.exists_linearCombination_eq | exact GlobalTheory.FirstOrderPoints.exists_linearCombination_eq | (intros; apply GlobalTheory.FirstOrderPoints.exists_linearCombination_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StProfileHolds
section
noncomputable section

open MvPolynomial
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1

theorem stProfile_holds : StProfile := by
  intro N
  induction N with
  | zero =>
    refine ⟨fun x => expNegInvGlue (1 - x), ?_, ?_, ?_, ?_⟩
    · exact expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
    · intro x hx
      exact expNegInvGlue.zero_of_nonpos (by linarith)
    · intro x
      simpa using expNegInvGlue.nonneg _
    · simpa using expNegInvGlue.pos_of_pos (x := 1) one_pos
  | succ N ih =>
    obtain ⟨G, h1, h2, h3, h4⟩ := ih
    have hc : Continuous G := h1.continuous
    have hd : deriv (fun x => ∫ s in (1:ℝ)..x, G s) = G := by
      funext x
      exact (hc.deriv_integral G 1 x)
    refine ⟨fun x => ∫ s in (1:ℝ)..x, G s, ?_, ?_, ?_, ?_⟩
    · rw [contDiff_infty_iff_deriv, hd]
      exact ⟨fun x => (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).differentiableAt, h1⟩
    · intro x hx
      have : ∫ s in (1:ℝ)..x, G s = ∫ s in (1:ℝ)..x, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le hx] at hs
        exact h2 s hs.1
      simpa using this
    · intro x
      rw [iteratedDeriv_succ', hd]
      exact h3 x
    · rw [iteratedDeriv_succ', hd]
      exact h4

example : GlobalTheory.PsCo.Pc1.StProfile := stProfile_holds

end GlobalTheory.PsCo.Pc1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRelIndexNeZeroParabolicStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_relIndex_ne_zero_parabolic : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ TM : Subgroup M, (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ (q : M) (X : N), (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) ≠ 0 := by
  first | exact @GlobalTheory.stab_relIndex_ne_zero | exact GlobalTheory.stab_relIndex_ne_zero | (intros; apply GlobalTheory.stab_relIndex_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementOfKernelExistsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_complement_of_adjoint_stable_kernel : ∀ (V W H : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (pr : V →ₗ[ℂ] W) (H0 : Submodule ℂ V), FiniteDimensional ℂ H0 → ∀ (A : Set (Module.End ℂ V)), (∀ a ∈ A, ∀ v ∈ H0, a v ∈ H0) → (∀ a ∈ A, ∀ v ∈ H0, pr v = 0 → pr (a v) = 0) → (∀ a ∈ A, ∃ b ∈ A, ∀ u v, inner ℂ (ι (a u)) (ι v) = inner ℂ (ι u) (ι (b v))) → ∀ h ∈ H0, ∃ c ∈ H0, pr c = pr h ∧ ∀ a ∈ A, ∀ z : ℂ, pr (a c) = z • pr c → a c = z • c := by
  first | exact @GlobalTheory.stable_complement_of_kernel_exists | exact GlobalTheory.stable_complement_of_kernel_exists | (intros; apply GlobalTheory.stable_complement_of_kernel_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleResStatement
section
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open : ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧ (f.stalkMap y).hom.EssFiniteType := by
  first | exact @GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | exact GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict | (intros; apply GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardEtaleMvPolynomialHypersurfaceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardEtale_localization_away_quotient_span : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∃ (f g : MvPolynomial (Option (Fin n)) A), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) ∧ (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : Option (Fin n) → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv none (MvPolynomial.map ψ f)) ≠ 0) ∧ Nonempty (B ≃ₐ[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)) := by
  first | exact @GlobalTheory.standardEtale_mvPolynomial_hypersurface | exact GlobalTheory.standardEtale_mvPolynomial_hypersurface | (intros; apply GlobalTheory.standardEtale_mvPolynomial_hypersurface <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Statement
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace GlobalTheory.CMTower

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def CMChain (v₀ : HeightOneSpectrum (𝓞 E)) (T T' : IntermediateField E Ω) : Prop :=
  ∃ (k : ℕ) (C : Fin (k + 1) → IntermediateField E Ω) (p : Fin k → ℕ) (hfd : ∀ i, FiniteDimensional E (C i)),
    C 0 = T ∧ C (Fin.last k) = T' ∧
    (∀ i, haveI := hfd i; haveI : NumberField (C i) := NumberField.of_module_finite E (C i); IsCMField (C i)) ∧
    (∀ i : Fin k, (p i).Prime ∧ ∃ h : C i.castSucc ≤ C i.succ,
      Module.finrank (C i.castSucc) (IntermediateField.extendScalars h) = p i ∧
      IsGalois (C i.castSucc) (IntermediateField.extendScalars h)) ∧
    ∀ i, haveI := hfd i; haveI : NumberField (C i) := NumberField.of_module_finite E (C i)
      ∀ v : HeightOneSpectrum (𝓞 (C i)), v.asIdeal.LiesOver v₀.asIdeal →
        v.asIdeal.ramificationIdx (𝓞 E) = Module.finrank E (C i)

def Statement : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w →
    ∀ (m : ℕ), 0 < m → ∀ (u ϖ : w.adicCompletion E), Valued.v u = 1 → Valued.v ϖ = WithZero.exp (-1) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))), w ∉ S →
    ∃ (k : ℕ) (T : Fin (k + 1) → IntermediateField E Ω) (p : Fin k → ℕ)
      (hfd : ∀ i, FiniteDimensional E (T i)),
      T 0 = ⊥ ∧
      (∀ i, haveI := hfd i; haveI : NumberField (T i) := NumberField.of_module_finite E (T i); IsCMField (T i)) ∧
      (∀ i : Fin k, (p i).Prime ∧ ∃ h : T i.castSucc ≤ T i.succ,
        Module.finrank (T i.castSucc) (IntermediateField.extendScalars h) = p i ∧
        IsGalois (T i.castSucc) (IntermediateField.extendScalars h)) ∧
      (haveI := hfd (Fin.last k); haveI : NumberField (T (Fin.last k)) := NumberField.of_module_finite E _
      ∃ (w'' : HeightOneSpectrum (𝓞 (T (Fin.last k)))) (_ : IsPlaceOver A w'')
          (_ : w''.asIdeal.LiesOver w.asIdeal),
        normV w'' = normV w ^ m ∧ w''.asIdeal.ramificationIdx (𝓞 E) = normV w ^ m - 1 ∧
        ∃ y : w''.adicCompletion (T (Fin.last k)),
          y ^ (normV w ^ m - 1) = KStar.Choice.complMap w w'' (u * ϖ)) ∧
      ∃ v₀ : HeightOneSpectrum (𝓞 E), v₀ ∉ S ∧ v₀ ≠ w ∧ ∀ i,
        haveI := hfd i; haveI : NumberField (T i) := NumberField.of_module_finite E (T i)
        ∀ v : HeightOneSpectrum (𝓞 (T i)), v.asIdeal.LiesOver v₀.asIdeal →
          v.asIdeal.ramificationIdx (𝓞 E) = Module.finrank E (T i)

end GlobalTheory.CMTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinitzPiIdealsLinearEquivOfClassGroupProd
section
open scoped nonZeroDivisors

namespace GlobalTheory.SteinitzProd

variable {R : Type} [CommRing R] [IsDedekindDomain R]

def coprimeEquiv (I J : Ideal R) (u v : R) (hu : u ∈ I) (hv : v ∈ J) (h : u + v = 1) :
    (I × J) ≃ₗ[R] ((⊤ : Ideal R) × (I * J : Ideal R)) where
  toFun p := (⟨p.1 + p.2, Submodule.mem_top⟩,
    ⟨v * p.1 - u * p.2, Ideal.sub_mem _ (mul_comm (p.1 : R) v ▸ Ideal.mul_mem_mul p.1.2 hv)
      (Ideal.mul_mem_mul hu p.2.2)⟩)
  invFun q := (⟨u * q.1 + q.2, add_mem (Ideal.mul_mem_right _ I hu)
      ((Ideal.mul_le_left (I := I) (J := J)) q.2.2)⟩,
    ⟨v * q.1 - q.2, Ideal.sub_mem _ (Ideal.mul_mem_right _ J hv)
      ((Ideal.mul_le_right (I := I) (J := J)) q.2.2)⟩)
  map_add' p q := by
    ext <;> simp <;> ring
  map_smul' c p := by
    ext <;> simp <;> ring
  left_inv p := by
    ext
    · simp only; linear_combination (p.1 : R) * h
    · simp only; linear_combination (p.2 : R) * h
  right_inv q := by
    ext
    · simp only; linear_combination (q.1 : R) * h
    · simp only; linear_combination (q.2 : R) * h

theorem classGroup_exists_integral_ideal_coprime {m : Ideal R} (hm : m ≠ ⊥) (c : ClassGroup R) :
    ∃ I : (Ideal R)⁰, (I : Ideal R) ⊔ m = ⊤ ∧ ClassGroup.mk0 I = c := by
  by_cases ht : m = ⊤
  · obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
    exact ⟨I, by rw [ht, sup_top_eq], hI⟩
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal R) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := (J : Ideal R) * m) (J := J)
    Ideal.mul_le_left (mul_ne_zero hJ0 hm)
  obtain ⟨M, hM⟩ : (J : Ideal R) ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 (ha ▸ le_sup_right)
  have h1 : m ⊔ M = ⊤ := by
    apply mul_left_cancel₀ hJ0
    rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact ht (by simpa using h1)
  refine ⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩, by rw [sup_comm]; exact h1, ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hJ0 hM0 (by simpa using hM.symm)
  rw [← inv_inv c, ← hJ, ClassGroup.mk0_eq_mk0_inv_iff]
  exact ⟨a, ha0, by rw [hM, mul_comm]⟩

theorem exists_prod_equiv (I J : (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ClassGroup.mk0 I * ClassGroup.mk0 J ∧
      Nonempty ((↥(I : Ideal R) × ↥(J : Ideal R)) ≃ₗ[R] (R × ↥(L : Ideal R))) := by
  have hJ0 : (J : Ideal R) ≠ ⊥ := by simpa using nonZeroDivisors.coe_ne_zero J
  obtain ⟨I', hcop, hcl⟩ := classGroup_exists_integral_ideal_coprime hJ0 (ClassGroup.mk0 I)
  have h1 : (1 : R) ∈ (I' : Ideal R) ⊔ J := by rw [hcop]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  refine ⟨I' * J, by rw [map_mul, hcl], ⟨?_⟩⟩
  have e1 := (GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq hcl.symm).some
  exact (e1.prodCongr (LinearEquiv.refl R _)) ≪≫ₗ coprimeEquiv _ _ u v hu hv huv ≪≫ₗ
    (Submodule.topEquiv.prodCongr (LinearEquiv.ofEq _ _ (Submonoid.coe_mul _ _ _).symm))

theorem exists_prod_pi_equiv (n : ℕ) : ∀ (I : Fin n → (Ideal R)⁰) (K : (Ideal R)⁰),
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ClassGroup.mk0 K * ∏ i, ClassGroup.mk0 (I i) ∧
      Nonempty ((↥(K : Ideal R) × ((i : Fin n) → ↥(I i : Ideal R))) ≃ₗ[R]
        (↥(L : Ideal R) × (Fin n → R))) := by
  induction n with
  | zero =>
    intro I K
    exact ⟨K, by simp, ⟨(LinearEquiv.refl R _).prodCongr (LinearEquiv.ofSubsingleton _ _)⟩⟩
  | succ n ih =>
    intro I K
    obtain ⟨L₁, hL₁, ⟨e₁⟩⟩ := exists_prod_equiv K (I 0)
    obtain ⟨L, hL, ⟨e₂⟩⟩ := ih (fun i => I i.succ) L₁
    refine ⟨L, by rw [hL, hL₁, Fin.prod_univ_succ, mul_assoc], ⟨?_⟩⟩
    exact (LinearEquiv.refl R _).prodCongr (Fin.consLinearEquiv R (fun i => ↥(I i : Ideal R))).symm ≪≫ₗ
      (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ e₁.prodCongr (LinearEquiv.refl R _) ≪≫ₗ
      LinearEquiv.prodAssoc R _ _ _ ≪≫ₗ (LinearEquiv.refl R R).prodCongr e₂ ≪≫ₗ
      (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ
      (LinearEquiv.prodComm R _ _).prodCongr (LinearEquiv.refl R _) ≪≫ₗ
      LinearEquiv.prodAssoc R _ _ _ ≪≫ₗ
      (LinearEquiv.refl R _).prodCongr (Fin.consLinearEquiv R (fun _ => R))

theorem exists_pi_equiv {ι : Type} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n + 1))
    (I : ι → (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ∏ i, ClassGroup.mk0 (I i) ∧
      Nonempty (((i : ι) → ↥(I i : Ideal R)) ≃ₗ[R] (↥(L : Ideal R) × (Fin n → R))) := by
  let I' : Fin (n + 1) → (Ideal R)⁰ := fun j => I (e.symm j)
  obtain ⟨L, hL, ⟨f⟩⟩ := exists_prod_pi_equiv n (fun j => I' j.succ) (I' 0)
  refine ⟨L, ?_, ⟨?_⟩⟩
  · rw [hL, ← Fin.prod_univ_succ (f := fun j => ClassGroup.mk0 (I' j))]
    exact Equiv.prod_comp e.symm (fun i => ClassGroup.mk0 (I i))
  · exact LinearEquiv.piCongrLeft' R (fun i => ↥(I i : Ideal R)) e ≪≫ₗ
      (Fin.consLinearEquiv R (fun j => ↥(I' j : Ideal R))).symm ≪≫ₗ f

theorem steinitz : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι]
    (I J : ι → (Ideal R)⁰), ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) →
    Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) := by
  intro R _ _ ι _ I J h
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
  let e : ι ≃ Fin (n + 1) := (Fintype.equivFin ι).trans (finCongr hn)
  obtain ⟨L, hL, ⟨f⟩⟩ := exists_pi_equiv e I
  obtain ⟨L', hL', ⟨f'⟩⟩ := exists_pi_equiv e J
  obtain ⟨g⟩ := GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq (R := R) (I := L) (J := L')
    (by rw [hL, hL', h])
  exact ⟨f ≪≫ₗ g.prodCongr (LinearEquiv.refl R _) ≪≫ₗ f'.symm⟩

end GlobalTheory.SteinitzProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleFgOfLocallyLeFgStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem : ∀ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing R] (M : Submodule R A) (s : Set R), Ideal.span s = ⊤ → (∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) → M.FG := by
  first | exact @GlobalTheory.submodule_fg_of_locally_le_fg | exact GlobalTheory.submodule_fg_of_locally_le_fg | (intros; apply GlobalTheory.submodule_fg_of_locally_le_fg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHadamardPosDefPosSemidefStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef : ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef → 0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  first | exact @GlobalTheory.sum_hadamard_posDef_posSemidef | exact GlobalTheory.sum_hadamard_posDef_posSemidef | (intros; apply GlobalTheory.sum_hadamard_posDef_posSemidef <;> assumption)
end

