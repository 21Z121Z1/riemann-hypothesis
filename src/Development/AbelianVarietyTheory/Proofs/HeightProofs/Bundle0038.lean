import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoordDnApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0035
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0036
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0037
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfIsTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke

section Gen
variable {M N : Type} [AddCommGroup M] [TopologicalSpace M] [AddCommGroup N] [TopologicalSpace N]

def SmoothAlong (Z : M → Prop) (f : M → ℂ) : Prop :=
  ∀ (k : ℕ) (L : (Fin k → ℝ) →+ M), Continuous L → (∀ t, Z (L t)) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)

theorem gen_smooth_iff {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] (Z : M → Prop)
    (r : P →+ M) (hr : Continuous r) (hZ : ∀ p, Z (r p)) (co : M →+ P) (hc : Continuous co)
    (h3 : ∀ z, Z z → r (co z) = z) (f : M → ℂ) :
    SmoothAlong Z f ↔ ∀ w, ContDiff ℝ ∞ fun p => f (w + r p) := by
  constructor
  · intro h w
    let e : P ≃L[ℝ] (Fin (Module.finrank ℝ P) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
    have := (h _ (r.comp e.symm.toLinearEquiv.toLinearMap.toAddMonoidHom) (hr.comp e.symm.continuous)
      (fun t => hZ _) w).comp e.contDiff
    convert this using 2 with p
    exact congrArg (fun q => f (w + r q)) (e.symm_apply_apply p).symm
  · intro h k L hL h0 w
    have := (h w).comp ((co.comp L).toRealLinearMap (hc.comp hL)).contDiff
    convert this using 2 with t
    exact congrArg (fun q => f (w + q)) (h3 _ (h0 t)).symm

theorem gen_smooth_comp (φ : M →+ N) (hφ : Continuous φ) (Z : M → Prop) (Z' : N → Prop) (hZ : ∀ x, Z x → Z' (φ x))
    (f : N → ℂ) (h : SmoothAlong Z' f) : SmoothAlong Z (f ∘ φ) := by
  intro k L hL h0 w
  have := h k (φ.comp L) (hφ.comp hL) (fun t => hZ _ (h0 t)) (φ w)
  convert this using 2 with t
  exact congrArg f (φ.map_add _ _)

theorem gen_smooth_equiv (φ : M ≃+ N) (h1 : Continuous φ) (h2 : Continuous φ.symm) (Z : M → Prop) (Z' : N → Prop)
    (hZ : ∀ x, Z' (φ x) ↔ Z x) (f : N → ℂ) : SmoothAlong Z' f ↔ SmoothAlong Z (f ∘ φ) := by
  refine ⟨gen_smooth_comp φ.toAddMonoidHom h1 Z Z' (fun x => (hZ x).2) f, fun h => ?_⟩
  have := gen_smooth_comp φ.symm.toAddMonoidHom h2 Z' Z (fun x hx => (hZ _).1 (by simpa using hx)) _ h
  convert this using 1
  funext x
  simp

theorem gen_level (φ : M ≃+ N) (h1 : Continuous φ) (h2 : Continuous φ.symm) (Z Q : M → Prop) (Z' Q' : N → Prop)
    (hZ : ∀ x, Z' (φ x) ↔ Z x) (hQ : ∀ x, Q' (φ x) ↔ Q x) :
    (∃ U : AddSubgroup N, IsOpen (U : Set N) ∧ ∀ u ∈ U, Z' u → Q' u) ↔
      ∃ U : AddSubgroup M, IsOpen (U : Set M) ∧ ∀ u ∈ U, Z u → Q u := by
  constructor
  · rintro ⟨U, hU, h⟩
    exact ⟨U.comap φ.toAddMonoidHom, hU.preimage h1, fun u hu h0 => (hQ u).1 (h _ hu ((hZ u).2 h0))⟩
  · rintro ⟨U, hU, h⟩
    refine ⟨U.comap φ.symm.toAddMonoidHom, hU.preimage h2, fun u hu h0 => ?_⟩
    obtain ⟨u, rfl⟩ := φ.surjective u
    exact (hQ u).2 (h u (by simpa using hu) ((hZ u).1 h0))

theorem gen_cont_equiv (φ : M ≃+ N) (h2 : Continuous φ.symm) (f : N → ℂ) (h : Continuous (f ∘ φ)) : Continuous f := by
  convert h.comp h2 using 1
  funext x
  simp

omit [TopologicalSpace M] [TopologicalSpace N] in
theorem gen_quasi (φ : M ≃+ N) (S : AddSubgroup M) (S' : AddSubgroup N) (hS : ∀ x, φ x ∈ S' ↔ x ∈ S)
    (κ : M → M → ℂ) (κ' : N → N → ℂ) (hκ : ∀ x y, κ' (φ x) (φ y) = κ x y) (f : N → ℂ) :
    (∀ γ ∈ S', ∀ w, f (γ + w) = κ' γ w * f w) ↔ ∀ γ ∈ S, ∀ w, (f ∘ φ) (γ + w) = κ γ w * (f ∘ φ) w := by
  simp only [φ.surjective.forall, hS, hκ, Function.comp_apply, map_add]

theorem gen_continuous [IsTopologicalAddGroup M] {A : Type} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] (ψ : AddChar A ℂ) (hψ : Continuous ψ) (s : M → M → A)
    (hs : Continuous fun p : M × M => s p.1 p.2) (R : M →+ M) (hR : Continuous R) (U : AddSubgroup M)
    (hU : IsOpen (U : Set M)) (g : M → ℂ) (h1 : ∀ w, Continuous fun d => g (w + R d))
    (h2 : ∀ d, d - R d ∈ U → ∀ x, ψ (s x (d - R d)) * g (x + (d - R d)) = g x) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro w₀
  have hd : Continuous fun w => w - w₀ := continuous_id.sub continuous_const
  have hu : Continuous fun w => (w - w₀) - R (w - w₀) := hd.sub (hR.comp hd)
  have hG : Continuous fun w => ψ (-s (w₀ + R (w - w₀)) ((w - w₀) - R (w - w₀))) * g (w₀ + R (w - w₀)) :=
    (hψ.comp (hs.comp ((continuous_const.add (hR.comp hd)).prodMk hu)).neg).mul ((h1 w₀).comp hd)
  refine hG.continuousAt.congr ?_
  filter_upwards [(hU.preimage hu).mem_nhds (show w₀ ∈ _ by simp)] with w hw
  rw [← h2 _ hw (w₀ + R (w - w₀)), ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
    one_mul]
  congr 1
  abel

theorem gen_cont_herm {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : ℕ} (σ : R →+* R)
    (hσ : Continuous σ) (Ji : Matrix (Fin a) (Fin a) R) (K : Matrix (Fin b) (Fin b) R) (ξ : R) :
    Continuous fun p : Matrix (Fin a) (Fin b) R × Matrix (Fin a) (Fin b) R =>
      ξ * Matrix.trace ((Ji * Formalism.UG.cT σ p.2ᵀ * K)ᵀᵀ * p.1ᵀ) :=
  continuous_const.mul
    (((continuous_const.matrix_mul (continuous_snd.matrix_transpose.matrix_map
      hσ).matrix_transpose).matrix_mul continuous_const).matrix_transpose.matrix_transpose.matrix_mul
        continuous_fst.matrix_transpose).matrix_trace

end Gen

def realMat (D : D7) (m n : ℕ) :
    (Fin m → Fin n → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)) →+ Matrix (Fin m) (Fin n) (AE D) :=
  AddMonoidHom.mk' (fun p => Matrix.of fun i j => HeisenbergWeilMatrices.realPt D (p i j)) fun p q =>
    Matrix.ext fun i j => (realPtHom D).map_add (p i j) (q i j)

theorem continuous_realMat (D : D7) (m n : ℕ) : Continuous (realMat D m n) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_realPt D).comp ((continuous_apply j).comp (continuous_apply i))

theorem exists_coMat (D : D7) (m n : ℕ) : ∃ co : Matrix (Fin m) (Fin n) (AE D) →+
    (Fin m → Fin n → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)), Continuous co ∧
    (∀ z, (z - realMat D m n (co z)).map (infPart D) = 0) ∧ ∀ z, z.map (finPart D) = 0 → realMat D m n (co z) = z := by
  obtain ⟨co, h1, h2, h3⟩ := exists_co D
  exact ⟨AddMonoidHom.mk' (fun z i j => co (z i j)) fun z w => funext₂ fun i j => co.map_add _ _,
    continuous_pi fun i => continuous_pi fun j => h1.comp ((continuous_apply j).comp (continuous_apply i)),
    fun z => Matrix.ext fun i j => h2 (z i j),
    fun z hz => Matrix.ext fun i j => h3 (z i j) (congrFun₂ hz i j)⟩

theorem smoothAlong_iff {m n : ℕ} (f : Matrix (Fin m) (Fin n) (AE D) → ℂ) :
    SmoothAlong (fun z => z.map (finPart D) = 0) f ↔ ∀ w, ContDiff ℝ ∞ fun p => f (w + realMat D m n p) := by
  obtain ⟨co, c1, -, c3⟩ := exists_coMat D m n
  exact gen_smooth_iff (fun z : Matrix (Fin m) (Fin n) (AE D) => z.map (finPart D) = 0) (realMat D m n) (continuous_realMat D m n)
    (fun p => Matrix.ext fun i j => finPart_realPt D (p i j)) co c1 c3 f

theorem continuous_cA (D : D7) : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap

theorem continuous_hsymp (A B : HSp D) : Continuous fun p : HeisenbergWeilMatrices.WA A B × HeisenbergWeilMatrices.WA A B => HeisenbergWeilMatrices.hsymp p.1 p.2 :=
  continuous_const.mul ((IsModuleTopology.continuous_of_linearMap (HeisenbergWeilMatrices.trA D)).comp
    (gen_cont_herm (cA D) (continuous_cA D) (HeisenbergWeilMatrices.gramInvA A) (HeisenbergWeilMatrices.gramA B) (incA D D.host.xi0)))

theorem continuous_of_isTheta {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {g : HeisenbergWeilMatrices.WA A B → ℂ}
    (hg : HeisenbergWeilMatrices.IsTheta ψ g) : Continuous g := by
  obtain ⟨-, hs, U, hU, hl⟩ := hg
  obtain ⟨co, c1, c2, -⟩ := exists_coMat D A.rank B.rank
  exact gen_continuous ψ hψ HeisenbergWeilMatrices.hsymp (continuous_hsymp A B) ((realMat D _ _).comp co)
    ((continuous_realMat D _ _).comp c1) U hU g (fun w => (hs w).continuous.comp c1)
    fun d hd x => congrFun (hl _ hd (c2 d)) x

end GlobalTheory.DualPairCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCapitulationFieldSizeStatement
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_capitulation_field_size : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∀ (F : IntermediateField ℚ ℂ) (a b : ℝ), Sz F a b → (∀ (τ : E →+* ℂ) x, τ x ∈ F) → ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + Real.log (classNumber E)) (b + Real.log (classNumber E)) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], F' ≤ K → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : K, β ≠ 0 ∧ Submodule.span (𝓞 K) {β} = ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧ ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  first | exact @GlobalTheory.FieldSize.exists_sz_typeNorm_principal | exact GlobalTheory.FieldSize.exists_sz_typeNorm_principal | (intros; apply GlobalTheory.FieldSize.exists_sz_typeNorm_principal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFieldIdealsPrincipalStatement
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_ideals_principal : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (F : IntermediateField ℚ ℂ) (a b : ℝ), Sz F a b → (∀ x, φ x ∈ F) → ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + Real.log (classNumber E)) (b + Real.log (classNumber E)) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], F' ≤ K → ∀ 𝔞 : Ideal (𝓞 E), ∃ β : K, Submodule.span (𝓞 K) {β} = Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = φ (a : E)} := by
  first | exact @GlobalTheory.FieldSize.exists_sz_capitulation | exact GlobalTheory.FieldSize.exists_sz_capitulation | (intros; apply GlobalTheory.FieldSize.exists_sz_capitulation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionTauCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj Matrix

section Data

variable {R : Type} [CommRing R] [IsDomain R]

end Data

section Transport

variable {A : Over (Sp ℂ)} [GrpObj A] {L M : LB A.left} {g : ℕ}

theorem valAt'_resU {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V (res h a).val = valAt' x U a.val :=
  valAt'_res x h _ hV

theorem iso_fr {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g) (z : Fin g → ℂ) {j j' : M.ι} {i i' : L.ι}
    (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U j) (hj' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U j')
    (hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) (hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i') :
    valAt' (u.ex z).left (M.U j ⊓ L.U i) (w.s (j, i)).val * u.fr i z =
      valAt' (u.ex z).left (M.U j ⊓ M.U j') (M.g j j').val *
        (valAt' (u.ex z).left (M.U j' ⊓ L.U i') (w.s (j', i')).val * u.fr i' z) := by
  have hO : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (M.U j ⊓ L.U i ⊓ (M.U j' ⊓ L.U i')) := fun p hp =>
    ⟨⟨hj hp, hi hp⟩, hj' hp, hi' hp⟩
  have hii : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U i') := fun p hp => ⟨hi hp, hi' hp⟩
  have e := congrArg (fun a : Γ(A.left, M.U j ⊓ L.U i ⊓ (M.U j' ⊓ L.U i'))ˣ => valAt' (u.ex z).left _ a.val)
    (hw (j, i) (j', i'))
  have e' : valAt' (u.ex z).left (M.U j ⊓ L.U i) (w.s (j, i)).val =
      valAt' (u.ex z).left (M.U j ⊓ M.U j') (M.g j j').val *
        (valAt' (u.ex z).left (L.U i ⊓ L.U i') (L.g i i').val)⁻¹ *
        valAt' (u.ex z).left (M.U j' ⊓ L.U i') (w.s (j', i')).val := by
    refine (valAt'_resU _ _ _ hO).symm.trans (e.trans ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·)
      ((valAt'_mul _ _ _ _).trans (congrArg₂ (· * ·) (valAt'_resU _ _ _ hO)
        ((valAt'_units_inv _ hO _).trans (congrArg (·⁻¹) (valAt'_resU _ _ _ hO))))) (valAt'_resU _ _ _ hO))))
  have hne := valAt'_unit_ne_zero _ hii (L.g i i')
  rw [e', u.fr_compat i i' z hii]
  field_simp

theorem valAt'_g_self {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) (x : Sp ℂ ⟶ X) {j : M.ι} (hj : ⊤ ≤ x ⁻¹ᵁ M.U j) :
    valAt' x (M.U j ⊓ M.U j) (M.g j j).val = 1 := by
  rw [← valAt'_resU x (le_inf le_rfl le_rfl : M.U j ≤ M.U j ⊓ M.U j) _ hj, hM.g_self, Units.val_one,
    valAt'_one x hj]

theorem exists_chart_ex (hL : L.IsLB) (u : HolUnif A L g) (z : Fin g → ℂ) :
    ∃ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := by
  obtain ⟨i, hi⟩ := exists_chart hL ((u.ex z).left (default : PrimeSpectrum ℂ))
  exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩

def frT (hL : L.IsLB) (w : LB.Iso L M) (u : HolUnif A L g) (j : M.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u.ex z).left (M.U j ⊓ L.U (exists_chart_ex hL u z).choose) (w.s (j, (exists_chart_ex hL u z).choose)).val *
    u.fr (exists_chart_ex hL u z).choose z

theorem frT_eq (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g) {j : M.ι} {i : L.ι}
    {z : Fin g → ℂ} (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U j) (hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    frT hL w u j z = valAt' (u.ex z).left (M.U j ⊓ L.U i) (w.s (j, i)).val * u.fr i z := by
  rw [frT, iso_fr hw u z hj hj (exists_chart_ex hL u z).choose_spec hi, valAt'_g_self hM _ hj, _root_.one_mul]

def transport (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g) : HolUnif A M g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := frT hL w u
  fr_hol j z₀ hz₀ := by
    obtain ⟨i, hi⟩ := exists_chart_ex hL u z₀
    have h₁ := u.hol (M.U j ⊓ L.U i) (w.s (j, i)).val
    have hm : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (M.U j ⊓ L.U i)} ∈ nhds z₀ :=
      h₁.1.mem_nhds ((top_le_preimage_inf _ _ _).2 ⟨hz₀, hi⟩)
    have hd := (h₁.2.mul ((u.fr_hol i).mono fun z hz => ((top_le_preimage_inf _ _ _).1 hz).2)).differentiableAt hm
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hm] with z hz
    exact frT_eq hL hM hw u ((top_le_preimage_inf _ _ _).1 hz).1 ((top_le_preimage_inf _ _ _).1 hz).2
  fr_ne j z hz := by
    have hi := (exists_chart_ex hL u z).choose_spec
    exact mul_ne_zero (valAt'_unit_ne_zero _ ((top_le_preimage_inf _ _ _).2 ⟨hz, hi⟩) _) (u.fr_ne _ _ hi)
  fr_compat j j' z hz :=
    have hi := (exists_chart_ex hL u z).choose_spec
    iso_fr hw u z ((top_le_preimage_inf _ _ _).1 hz).1 ((top_le_preimage_inf _ _ _).1 hz).2 hi hi

theorem isAH_transport (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) : (transport hL hM hw u).IsAH Hm χ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun l j z hj => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart_ex hL u z
  have hl : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
  have a := frT_eq hL hM hw u (z := z) hj hi
  have b := frT_eq hL hM hw u (j := j) (i := i) (z := z + l) (by rw [hl]; exact hj) (by rw [hl]; exact hi)
  rw [hl] at b
  refine a.trans (Eq.trans ?_ (congrArg _ b.symm))
  rw [h.2.2.2 l i z hi]
  ring

end Transport

theorem isGen_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
    LB.Gen.IsGen (⟨fun p => L.g p.1 p.2⟩ : LB.Iso L L) := by
  refine fun p q => unit_ext fun y hy => ?_
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

def polOfPullback {S S' : Scheme.{0}} (P : Out.PolAV S) {f : S' ⟶ S} (A : Over S') [GrpObj A] [IsCommMonObj A]
    {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A f φ) : Out.PolAV S' where
  A := A
  isAb :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 P.isAb.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 P.isAb.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 P.isAb.geomConnected }
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
  L := P.L.pull φ
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull h P.rigid
  sym := PolBaseChange.sym_pull h P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample h.1
  ktriv := kTriv_pull h P.isLB (pull_isLB P.isLB _) ((isGen_iff _).1 (isGen_refl (pull_isLB P.isLB φ))) P.ktriv

end GlobalTheory.TorsionTauCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPMulCongrFrobeniusOfPrimeNormStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_mul_congr_frobenius_of_primeNorm : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (α : ℂ) (p : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → p.Prime → (p : ℂ) ∈ W.nonunits → α ∈ W.nonunits → (∀ l ∈ L.lattice, α * l ∈ L.lattice) → ‖α‖ ^ 2 = p → ∃ a : ℂ, a ∈ W ∧ a⁻¹ ∈ W ∧ a ≠ 0 ∧ L.g₂ - a ^ 2 * L.g₂ ^ p ∈ W.nonunits ∧ L.g₃ - a ^ 3 * L.g₃ ^ p ∈ W.nonunits ∧ ∀ (m : ℕ) (t : ℂ), 0 < m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP (α * t) - a * L.weierstrassP t ^ p ∈ W.nonunits := by
  first | exact @GlobalTheory.EisensteinCongruence.weierstrassP_mul_congr_pow_of_pos | exact GlobalTheory.EisensteinCongruence.weierstrassP_mul_congr_pow_of_pos | (intros; apply GlobalTheory.EisensteinCongruence.weierstrassP_mul_congr_pow_of_pos <;> assumption)
end

