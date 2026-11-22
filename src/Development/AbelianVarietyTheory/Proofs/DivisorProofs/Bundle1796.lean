import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1762
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldTensorOfIsEmptyAlgHom
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweLocal.Fld

open Polynomial
open scoped IntermediateField

theorem isField_tensor_of_isEmpty_algHom {F K E : Type} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] (h2 : Module.finrank F E = 2) (hE : IsEmpty (E →ₐ[F] K)) :
    IsField (K ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have hne : (⊥ : IntermediateField F E) ≠ ⊤ := by
    intro h
    rw [IntermediateField.bot_eq_top_iff_finrank_eq_one] at h
    omega
  obtain ⟨a, ha⟩ : ∃ a : E, a ∉ (⊥ : IntermediateField F E) := by
    by_contra h
    push_neg at h
    exact hne (eq_top_iff.2 fun z _ => h z)
  have hint : IsIntegral F a := Algebra.IsIntegral.isIntegral a
  have hnot : a ∉ (algebraMap F E).range := fun h => ha (IntermediateField.mem_bot.2 h)
  have hge : 2 ≤ (minpoly F a).natDegree := (minpoly.two_le_natDegree_iff hint).2 hnot
  have hle : (minpoly F a).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le a
  obtain ⟨b, c, hbc⟩ := isMonicOfDegree_two_iff.1
    (⟨by omega, minpoly.monic hint⟩ : IsMonicOfDegree (minpoly F a) 2)
  have hq : a ^ 2 + algebraMap F E b * a + algebraMap F E c = 0 := by
    have := minpoly.aeval F a
    rw [hbc] at this
    simpa [Algebra.smul_def] using this
  refine GlobalTheory.InertField.isField_tensor_of_no_root h2 a (fun x hx => hnot ⟨x, hx⟩) b c hq
    fun x hx => hE.false ?_
  have hroot : aeval x (minpoly F a) = 0 := by
    rw [hbc]
    simpa [Algebra.smul_def] using hx
  have htop : F⟮a⟯ = ⊤ := by
    refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
    rw [IntermediateField.adjoin.finrank hint, IntermediateField.finrank_top', h2]
    omega
  exact ((IntermediateField.adjoin.powerBasis hint).lift x
      (by rwa [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen])).comp
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).symm.toAlgHom

theorem isField_of_isEmpty : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → IsField (Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ hCM v hv
  exact isField_tensor_of_isEmpty_algHom hCM.2.2.1 hv

end GlobalTheory.HoweLocal.Fld
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocCoLocDarboux
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.LocCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_mul (v : Pl F) (a : Fv F v) (b : AF F) :
    GlobalTheory.LatVac.liftV v a * b = GlobalTheory.LatVac.liftV v (a * evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v a * b.2 = GlobalTheory.AdelicU.singleFin v (a * evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem liftV_smul_liftE (v : Pl F) (a : Fv F v) (z : Fv F v ⊗[F] E) :
    GlobalTheory.LatVac.liftV v a • liftE (E := E) v z = liftE v (a • z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, smul_add, hx, hy, smul_add, map_add]
  | tmul b e =>
    rw [TensorProduct.smul_tmul', liftE, TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, liftV_mul, GlobalTheory.LatVac.evFin_liftV]

theorem compFin_liftE (v : Pl F) (z : Fv F v ⊗[F] E) : compFin F E v (liftE v z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b e =>
    rw [liftE, TensorProduct.map_tmul]
    change evFin F v (GlobalTheory.LatVac.liftV v b) ⊗ₜ[F] e = b ⊗ₜ[F] e
    rw [GlobalTheory.LatVac.evFin_liftV]

theorem liftV_one_smul (v : Pl F) (z : AE F E) :
    GlobalTheory.LatVac.liftV v 1 • z = liftE v (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]
  | tmul b e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_mul, one_mul]
    change _ = liftE v (evFin F v b ⊗ₜ[F] e)
    rw [liftE, TensorProduct.map_tmul]
    rfl

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl F) (z : AE F E) :
    compFin F E v (cA σ z) = cv σ v (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul b e => rfl

theorem trace_tmul (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem evFin_trace (v : Pl F) (z : AE F E) :
    evFin F v (Algebra.trace (AF F) (AE F E) z) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul b e =>
    change _ = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (evFin F v b ⊗ₜ[F] e)
    rw [trace_tmul, trace_tmul, map_mul, AlgHom.commutes]

end GlobalTheory.HoweLocal.LocCoords

namespace GlobalTheory.HoweLocal.LocCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symp_lift (σ : E →ₐ[F] E) (v : Pl F) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x x' : Matrix (Fin n) (Fin d) (Fv F v ⊗[F] E)) :
    symp (R := Fv F v) (cv σ v) (-1) (Jv v JX) (Jv v JW) x x' =
      evFin F v (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) (x.map (liftE v)) (x'.map (liftE v))) := by
  unfold symp hTens
  rw [evFin_trace]
  congr 1
  simp only [map_mul, map_neg, map_one, map_sum, Matrix.map_apply, compFin_cA, compFin_liftE]
  rfl

def locE (σ : E →ₐ[F] E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F) :
    Matrix (Fin n) (Fin d) (Fv F v ⊗[F] E) ≃ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) where
  toFun x := GlobalTheory.LatVac.locCo M.co v (x.map (liftE v))
  map_add' x y := by rw [Matrix.map_add _ (map_add _), map_add]
  map_smul' a x := by
    have h : (a • x).map (liftE v) = GlobalTheory.LatVac.liftV v a • x.map (liftE v) := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, liftV_smul_liftE]
    simp only [RingHom.id_apply, h, GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
    ext k
    · simp [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, liftV_mul, GlobalTheory.LatVac.evFin_liftV]
    · simp [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, liftV_mul, GlobalTheory.LatVac.evFin_liftV]
  invFun p := (M.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k))).map
    (compFin F E v)
  left_inv x := by
    have h1 : GlobalTheory.LatVac.liftV v 1 • x.map (liftE v) = x.map (liftE v) := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, liftV_smul_liftE, one_smul]
    have h2 : ((fun k => GlobalTheory.LatVac.liftV v ((GlobalTheory.LatVac.locCo M.co v (x.map (liftE v))).1 k),
        fun k => GlobalTheory.LatVac.liftV v ((GlobalTheory.LatVac.locCo M.co v (x.map (liftE v))).2 k)) :
          (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) = M.co.e (x.map (liftE v)) := by
      conv_rhs => rw [← h1, map_smul]
      ext k
      · simp [GlobalTheory.LatVac.locCo, liftV_mul]
      · simp [GlobalTheory.LatVac.locCo, liftV_mul]
    simp only
    rw [h2, LinearEquiv.symm_apply_apply]
    ext i j; simp [compFin_liftE]
  right_inv p := by
    set y := M.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)) with hy
    have h1 : (y.map (compFin F E v)).map (liftE v) = GlobalTheory.LatVac.liftV v 1 • y := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, liftV_one_smul]
    simp only
    rw [h1]
    show (fun k => evFin F v ((M.co.e (GlobalTheory.LatVac.liftV v 1 • y)).1 k),
      fun k => evFin F v ((M.co.e (GlobalTheory.LatVac.liftV v 1 • y)).2 k)) = p
    rw [map_smul, hy, LinearEquiv.apply_symm_apply]
    ext k <;> simp [liftV_mul, GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.HoweLocal.LocCoords

namespace GlobalTheory.HoweLocal.LocCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def locDarboux (σ : E →ₐ[F] E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F) :
    Darboux (symp (R := Fv F v) (cv σ v) (-1) (Jv v X.J) (Jv v W.J)) (Fin n × Fin d) where
  e := locE σ M v
  form x x' := by
    rw [symp_lift, M.co.form]
    simp only [locE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, dotProduct, map_sub, map_sum, map_mul]

theorem isLocCo_locDarboux (σ : E →ₐ[F] E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F) :
    IsLocCo σ M v (locDarboux σ M v) := fun _ => rfl

end GlobalTheory.HoweLocal.LocCoords

theorem GlobalTheory.HoweLocal.exists_isLocCo : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (v : Pl F),
      ∃ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J))
        (Fin n × Fin d), GlobalTheory.HoweLocal.IsLocCo σ M v co :=
  fun _ _ _ _ _ _ _ σ _ _ _ _ _ M v => ⟨_, GlobalTheory.HoweLocal.LocCoords.isLocCo_locDarboux σ M v⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunctionStatement
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
theorem _root_.GlobalTheory.T.isLocallyConstant_heisenberg_lattice_vacuum_function : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    IsOpen (Λ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ (χ : (κ → Fv F v) × (κ → Fv F v) → ℂ) (x₀ : κ → Fv F v),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : Fv F v) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → Fv F v, ((0 : κ → Fv F v), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, χ (u + u) = 1) → IsLocallyConstant (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) := by
  first | exact @GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place | exact GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place | (intros; apply GlobalTheory.HeisLatVac.isLocallyConstant_vacFn_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour

variable {F : Type} [Field F] [NumberField F]

def IsSelfDualFor {v : Pl F} (χ : AddChar (Fv F v) ℂ) (ν : Measure (Fv F v)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∀ f ∈ SB (Fv F v), ∫ y, (∫ x, f x * χ (x * y) ∂ν) ∂ν = f 0

open Classical in

def measV (ψ : AddChar (AF F) ℂ) (v : Pl F) : Measure (Fv F v) :=
  if h : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν then h.choose else 0

def fourV (ψ : AddChar (AF F) ℂ) (v : Pl F) {κ : Type} [Fintype κ] (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) : ℂ :=
  ∫ x, φ x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y) ∂(Measure.pi fun _ : κ => measV ψ v)

open Classical in
variable (F) in

def measI (κ : Type) [Fintype κ] : Measure (κ → mixedEmbedding.mixedSpace F) :=
  Measure.pi fun _ : κ => (Measure.pi fun _ : {w : InfinitePlace F // w.IsReal} => (volume : Measure ℝ)).prod
    (Measure.pi fun _ : {w : InfinitePlace F // w.IsComplex} => (volume : Measure ℂ))

def eInf {κ : Type} [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ))

end GlobalTheory.WeylFour

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddCharStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsStdChar D ψ (-1) := by
  first | exact @GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd | exact GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd | (intros; apply GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeWeightMemConeOverLowestKType
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.kType_weight_in_cone_over_lowK : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  intro n ε H _ _ σ D E lam hP hC hDS hK μ S hS
  have hcomp : CompleteSpace H := hDS.1
  have hU : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hI : IsIrredOn (UJset ε) σ := hDS.2.2.2.1
  obtain ⟨w, hw0, -, hwH⟩ := hK.hw μ S hS
  have key : ∃ T : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) T ∧ ∃ x ∈ T.comap D.subtype,
      ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
        ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 := by
    by_contra hne
    let Q : Submodule ℂ D :=
      { carrier := {x | ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) →
          ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ = 0}
        add_mem' := by
          intro a b ha hb l hl
          rw [map_add, inner_add_right, ha l hl, hb l hl, add_zero]
        zero_mem' := by
          intro l hl
          rw [map_zero, inner_zero_right]
        smul_mem' := by
          intro c a ha l hl
          rw [map_smul, inner_smul_right, ha l hl, mul_zero] }
    have hT : ∀ T ∈ {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S}, T ≤ Q.map D.subtype := by
      intro T hT y hy
      have hTD := (GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hcomp hU hI hK _ T hT).1
      refine ⟨⟨y, hTD hy⟩, ?_, rfl⟩
      intro l hl
      by_contra h
      exact hne ⟨T, hT, ⟨y, hTD hy⟩, hy, l, hl, h⟩
    have hlow : lowKSub ε lam σ ≤ Q.map D.subtype := sSup_le hT
    have hspan := GlobalTheory.T.kFinite_span_raisingOperator_words_lowestKType n ε H σ D E lam hP hC hDS hK
    have hle : Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
        ∃ x ∈ (lowKSub ε lam σ).comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} ≤
        (ℂ ∙ w)ᗮ := by
      rw [Submodule.span_le]
      rintro y ⟨l, hl, x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      obtain ⟨x', hx', hxx⟩ := hlow hx
      have : x' = x := Subtype.ext hxx
      subst this
      exact hx' l hl
    rw [hspan] at hle
    have hw : w ∈ (ℂ ∙ w)ᗮ := hle Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hw
    exact hw0 hw
  obtain ⟨T, hT, x, hx, l, hl, hne⟩ := key
  have hadj := GlobalTheory.T.inner_word_ne_zero_reversedWord_ne_zero n ε D E hK.unit l w x hne
  obtain ⟨-, hfd, hstab, hhw⟩ := GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hcomp hU hI hK _ T hT
  have hl' : ∀ p ∈ l.reverse.map Prod.swap, ε p.1 = false ∧ ε p.2 = true := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [List.mem_reverse] at hq
    exact ⟨(hl q hq).2, (hl q hq).1⟩
  have hKU : KUnit ε E := fun a b hab y z => Formalism.REAL.isUnitary_kUnit ε E hK.unit a b hab y z
  obtain ⟨l', -, hl'ty, hsum⟩ := GlobalTheory.T.word_reaching_irreducible_k_module_reaches_highest_weight n ε D E hK.gl hKU (T.comap D.subtype) hfd hstab (lowK ε lam) hhw
    μ w hwH false true _ hl' x hx hadj
  exact GlobalTheory.root_word_count_letters n ε μ (lowK ε lam) l' hl'ty hsum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRouteBigVertexRationalLeftInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_route_big_vertex_rational_left_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g : GA D (G.V (.grid i (j + 1))), kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := by
  first | exact @GlobalTheory.BigRouteInv.kerBig_rat_mul | exact GlobalTheory.BigRouteInv.kerBig_rat_mul | (intros; apply GlobalTheory.BigRouteInv.kerBig_rat_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordinateUniqueNeZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_coordinate_unique_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i : M.K.bundle.ι) (k : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k → (∀ x y : K, KSRel M i k z x → KSRel M i k z y → x = y) ∧ ∀ x : K, KSRel M i k z x → x ≠ 0 := by
  first | exact @GlobalTheory.CompHS.ksRel_unique_ne_zero | exact GlobalTheory.CompHS.ksRel_unique_ne_zero | (intros; apply GlobalTheory.CompHS.ksRel_unique_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceNotDvdDifferentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.large_place_not_dvd_different : ∀ {D : D7} (large₂ : SizeData₂ D), Rec large₂ → ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∈ S1 D → ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  first | exact @GlobalTheory.DiffSOne.not_dvd_differentIdeal | exact GlobalTheory.DiffSOne.not_dvd_differentIdeal | (intros; apply GlobalTheory.DiffSOne.not_dvd_differentIdeal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeEqSublatticeDegreeAddLogIndexStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (m : ℕ) (L N : Submodule (𝓞 K) V), N ≤ L → L.FG → latRank K L = m → latRank K N = m → idx K m L N ≠ ⊥ ∧ deg h L = deg h N + Real.log (Ideal.absNorm (idx K m L N)) / Module.finrank ℚ K := by
  first | exact @GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx | exact GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx | (intros; apply GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantIndexIdealMapInjectiveEqColon
section
set_option autoImplicit false
noncomputable section
open NumberField

namespace GlobalTheory.IdxMap

theorem dets_eq_detSpan (F : Type) [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) :
    GlobalTheory.IdxTensor.dets F p L = GlobalTheory.BetaEx.detSpan L := by
  unfold GlobalTheory.IdxTensor.dets GlobalTheory.BetaEx.detSpan
  congr 1
  ext d
  rw [GlobalTheory.BetaEx.mem_detSet]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Matrix.of y, hy, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

theorem idx_map_eq_colon_dets : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := by
  intro F V _ _ _ _ _ _ p φ hφ L N
  set v : Fin p → V := fun i => φ (Pi.basisFun F (Fin p) i) with hv
  have hli : LinearIndependent F v :=
    (Pi.basisFun F (Fin p)).linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have hcoord : φ.restrictScalars (𝓞 F) = GlobalTheory.LatIndexDeg.coordMap F v := by
    refine LinearMap.ext fun x => ?_
    rw [GlobalTheory.LatIndexDeg.coordMap_apply, LinearMap.restrictScalars_apply]
    conv_lhs => rw [← (Pi.basisFun F (Fin p)).sum_repr x]
    simp [hv, map_sum, map_smul]
  have hω := GlobalTheory.LatIndexDeg.ιMulti_ne_zero_of_li v hli
  have hℓ : Function.Injective (GlobalTheory.LatIndexDeg.lineMap F (exteriorPower.ιMulti F p v)) :=
    fun s t e => smul_left_injective F hω e
  unfold GlobalTheory.FlatCM.idx
  rw [hcoord, GlobalTheory.LatIndexDeg.detSpan_map_coord, GlobalTheory.LatIndexDeg.detSpan_map_coord,
    GlobalTheory.LatIndexDeg.colon_map_of_injective _ hℓ, dets_eq_detSpan, dets_eq_detSpan]

end GlobalTheory.IdxMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantSpanSpanEqGeneratorDetsStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDeterminantSpan_span_eq_generator_dets : ∀ {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)),
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := by
  first | exact @GlobalTheory.IdxTensor.dets_span_eq | exact GlobalTheory.IdxTensor.dets_span_eq | (intros; apply GlobalTheory.IdxTensor.dets_span_eq <;> assumption)
end

