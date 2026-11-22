import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorRationalFormConjEqConjTable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.JetDescent

theorem coe_lift_of_mem (M : IntermediateField ℚ ℂ) (x : ℂ) (hx : x ∈ M) : Formalism.MainNotions.TaylorLogMetric.liftM M x = ⟨x, hx⟩ := by
  unfold Formalism.MainNotions.TaylorLogMetric.liftM
  exact dif_pos hx

theorem mapVV_rational_form_conj : ∀ {D : D7} {a b : ℕ} (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b) (n : D.what₂.Tau → ℕ)
    (J : (Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (σ : D.what₂.LL →+* ℂ) (ρ' : Qbar →ₐ[ℚ] ℂ)
    (f : VV D.what₂.LL lam →ₗ[D.what₂.LL] VV D.what₂.LL lam'), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ m, J m ∈ Qbar) →
    (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) →
    (∀ u, Formalism.L2.Ker.jetOp lam lam' J n (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u) = GlobalTheory.CoefModel.mapVV D.what₂.embLL lam' (f u)) →
    ∀ u, GlobalTheory.CoefModel.mapVV σ lam' (f u) =
      Formalism.L2.Ker.jetOp lam lam' (fun m => Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (J m)) n (GlobalTheory.CoefModel.mapVV σ lam u) := by
  intro D a b lam lam' n J σ ρ' f hV hJ hσ hf u
  have halg : ∀ x : D.what₂.LL, D.what₂.embLL x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.what₂.embLL.toRatAlgHom
  let e : D.what₂.LL →+* Qbar := D.what₂.embLL.codRestrict Qbar halg
  let i : Qbar →+* ℂ := algebraMap Qbar ℂ
  let r : Qbar →+* ℂ := ρ'
  let Jq : (Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ) → Qbar := fun m => ⟨J m, hJ m⟩
  have hie : i.comp e = D.what₂.embLL := RingHom.ext fun _ => rfl
  have hre : r.comp e = σ := RingHom.ext fun x => by
    rw [← hσ x]
    unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [coe_lift_of_mem _ _ (halg x)]
    rfl
  have hJi : (fun m => i (Jq m)) = J := funext fun _ => rfl
  have hJr : (fun m => r (Jq m)) = fun m => Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (J m) := funext fun m => by
    unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [coe_lift_of_mem _ _ (hJ m)]
    rfl
  have h1 : Formalism.L2.Ker.jetMap J n (MvPolynomial.map D.what₂.embLL u.1) = MvPolynomial.map D.what₂.embLL (f u).1 := by
    have h := congrArg Subtype.val (hf u)
    rw [Formalism.L2.Ker.jetOp_coe lam lam' n hV] at h
    exact h
  have h2 : Formalism.L2.Ker.jetMap Jq n (MvPolynomial.map e u.1) = MvPolynomial.map e (f u).1 := by
    apply MvPolynomial.map_injective i i.injective
    rw [Formalism.L2.Ker.map_jetMap, MvPolynomial.map_map, MvPolynomial.map_map, hie, hJi]
    exact h1
  have h3 := congrArg (MvPolynomial.map r) h2
  rw [Formalism.L2.Ker.map_jetMap, MvPolynomial.map_map, MvPolynomial.map_map, hre, hJr] at h3
  apply Subtype.ext
  rw [Formalism.L2.Ker.jetOp_coe lam lam' n hV]
  exact h3.symm

end GlobalTheory.JetDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianColumnsLinearParametrisationFinitePlac
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertLagParam

open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev lift (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E := (liftV v).rTensor E

theorem compFin_lift (v : Pl F) (t : Fv F v ⊗[F] E) : compFin F E v (lift v t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [compFin, evFin_liftV]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem liftV_one_smul_eq (v : Pl F) (a : AE F E) : liftV v (1 : Fv F v) • a = lift v (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin]
  | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]

theorem compFin_smul (v : Pl F) (r : AF F) (a : AE F E) : compFin F E v (r • a) = evFin F v r • compFin F E v a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [compFin, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem at_map_lift {α β : Type} (v : Pl F) (A : Matrix α β (Fv F v ⊗[F] E)) : At (evFin F v) (A.map (lift v)) := by
  intro u hu
  ext i k
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  induction A i k using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    rw [← smul_eq_mul, at_liftV v x u hu, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

theorem eq_map_lift {α β : Type} (v : Pl F) (z : Matrix α β (AE F E)) (hz : At (evFin F v) z) :
    z = (z.map (compFin F E v)).map (lift v) := by
  conv_lhs => rw [← liftV_one_smul v z hz]
  ext i k
  simp only [Matrix.smul_apply, Matrix.map_apply, liftV_one_smul_eq]

theorem map_lift_compFin {α β : Type} (v : Pl F) (A : Matrix α β (Fv F v ⊗[F] E)) :
    (A.map (lift v)).map (compFin F E v) = A := by
  ext i k; simp [compFin_lift]

end GlobalTheory.InertLagParam
end

namespace GlobalTheory.InertLagParam
open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem card_eq_of_inv {R : Type} [CommRing R] [Nontrivial R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (A : Matrix α β R) (B : Matrix β α R) (h1 : A * B = 1) (h2 : B * A = 1) :
    Fintype.card α = Fintype.card β := by
  let f : (β → R) ≃ₗ[R] (α → R) := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := f.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at this
  exact this.symm

theorem eq_zero_of_locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (v : Pl F) (u : W) (hu : At (evFin F v) u) (h0 : locCo co v u = 0) : u = 0 := by
  have h1 : co.e u = liftV v (1 : Fv F v) • co.e u := by rw [← LinearEquiv.map_smul, liftV_one_smul v u hu]
  have h2 : co.e u = 0 := by
    rw [h1]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · have := congrArg (fun p => p.1 k) h0
      simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_zero, Pi.zero_apply] at this
      simp [liftV_one_mul, this]
    · have := congrArg (fun p => p.2 k) h0
      simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.snd_zero, Pi.zero_apply] at this
      simp [liftV_one_mul, this]
  exact co.e.map_eq_zero_iff.1 h2

end GlobalTheory.InertLagParam

namespace GlobalTheory.InertLagParam

def mulLeft {R : Type} [CommRing R] (n m : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin m) R →ₗ[R] Matrix (Fin n) (Fin m) R where
  toFun x := A * x
  map_add' x y := Matrix.mul_add A x y
  map_smul' c x := Matrix.mul_smul A c x

theorem det_mulLeft {R : Type} [CommRing R] (n m : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    LinearMap.det (mulLeft n m A) = A.det ^ m := by
  let τ : Matrix (Fin n) (Fin m) R ≃ₗ[R] (Fin m → Fin n → R) :=
    { toFun := fun x k i => x i k
      invFun := fun y => Matrix.of fun i k => y k i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : (τ : _ →ₗ[R] _) ∘ₗ mulLeft n m A ∘ₗ (τ.symm : (Fin m → Fin n → R) →ₗ[R] _) =
      LinearMap.pi fun k : Fin m => Matrix.toLin' A ∘ₗ LinearMap.proj k := by
    refine LinearMap.ext fun y => ?_
    funext k i
    rfl
  rw [← LinearMap.det_conj (mulLeft n m A) τ, h, LinearMap.det_pi]
  simp [LinearMap.det_toLin']

end GlobalTheory.InertLagParam

namespace GlobalTheory.InertLagParam
open GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagUniq

theorem param : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (v : Pl F)
    (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    d = 2 * m ∧ ∃ (N : ℕ) (j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
      (ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E)), Function.Injective j ∧
      (∀ y, At (evFin F v) (ζ y) ∧ locCo M.co v (ζ y * Cᵀ) = j y) ∧
      (∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z → ∃ y, ζ y = z) ∧
      ∀ s : GL (Fin n) (AE F E), ∃ T : GL (Fin N) (Fv F v), (∀ y, ζ (T.val *ᵥ y) = s.val * ζ y) ∧
        T.val.det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
  intro F E _ _ _ _ _ σ n d X W M v m C hC
  obtain ⟨h0, Cx, P, hx, h1, h2⟩ := hC
  have hP1 : P.toRows₁ * C.map (compFin F E v) = 1 := by
    have h2' := h2
    rw [← Matrix.fromRows_toRows P, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one,
      Matrix.fromBlocks_inj] at h2'
    exact h2'.1
  refine ⟨?_, ?_⟩
  · have := card_eq_of_inv _ _ h1 h2
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  let Z := Matrix (Fin n) (Fin m) (Fv F v ⊗[F] E)
  let N := Module.finrank (Fv F v) Z
  let e : (Fin N → Fv F v) ≃ₗ[Fv F v] Z := (Module.finBasis (Fv F v) Z).equivFun.symm
  let ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E) := fun y => (e y).map (lift v)
  have hζat : ∀ y, At (evFin F v) (ζ y) := fun y => at_map_lift v _
  have hζc : ∀ y, (ζ y).map (compFin F E v) = e y := fun y => map_lift_compFin v _
  have hζadd : ∀ y y', ζ (y + y') = ζ y + ζ y' := fun y y' => by
    simp only [ζ, map_add]
    exact Matrix.map_add _ (map_add _) _ _
  have hζsmul : ∀ (a : Fv F v) y, ζ (a • y) = liftV v a • ζ y := fun a y => by
    have hat : At (evFin F v) (liftV v a • ζ y) := fun u hu => by rw [smul_comm, hζat y u hu, smul_zero]
    rw [eq_map_lift v _ hat]
    congr 1
    ext i k
    simp [ζ, compFin_smul, evFin_liftV, compFin_lift] <;> rfl
  let j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun y => locCo M.co v (ζ y * Cᵀ)
      map_add' := fun y y' => by rw [hζadd, Matrix.add_mul, map_add]
      map_smul' := fun a y => by
        rw [hζsmul, Matrix.smul_mul]
        ext k <;> simp [locCo, evFin_liftV, -Matrix.smul_mul] }
  refine ⟨N, j, ζ, ?_, fun y => ⟨hζat y, rfl⟩, fun z hz => ?_, fun s => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hu := eq_zero_of_locCo M.co v _ (at_mul v _ (hζat y) _) hy
    have h3 : e y * (C.map (compFin F E v))ᵀ = 0 := by
      have := congrArg (fun x => Matrix.map x (compFin F E v)) hu
      simp only [Matrix.map_mul, Matrix.transpose_map, hζc, Matrix.map_zero _ (map_zero _)] at this
      exact this
    have h4 : e y = 0 := by
      have h5 : e y = e y * (P.toRows₁ * C.map (compFin F E v))ᵀ := by
        rw [hP1, Matrix.transpose_one, Matrix.mul_one]
      rw [h5, Matrix.transpose_mul, ← Matrix.mul_assoc, h3, Matrix.zero_mul]
    exact e.map_eq_zero_iff.1 h4
  · exact ⟨e.symm (z.map (compFin F E v)), by simp only [ζ, LinearEquiv.apply_symm_apply]; exact (eq_map_lift v z hz).symm⟩
  · let sv := s.val.map (compFin F E v)
    let L : Z →ₗ[Fv F v] Z := (mulLeft n m sv).restrictScalars (Fv F v)
    let f := e.symm.toLinearMap ∘ₗ L ∘ₗ e.toLinearMap
    have hdet : (LinearMap.toMatrix' f).det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
      rw [LinearMap.det_toMatrix']
      have hf : f = e.symm.toLinearMap ∘ₗ L ∘ₗ e.symm.symm.toLinearMap := rfl
      rw [hf, LinearMap.det_conj, LinearMap.det_restrictScalars, det_mulLeft, map_pow, RingHom.map_det]
      rfl
    have hs : IsUnit s.val.det := by simpa using (Matrix.GeneralLinearGroup.det s).isUnit
    have hne : (LinearMap.toMatrix' f).det ≠ 0 := by
      rw [hdet]
      exact (((hs.map (compFin F E v)).map (Algebra.norm (Fv F v))).pow m).ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hne, fun y => ?_, hdet⟩
    show ζ (LinearMap.toMatrix' f *ᵥ y) = s.val * ζ y
    rw [LinearMap.toMatrix'_mulVec]
    have hat : At (evFin F v) (s.val * ζ y) := fun u hu => by rw [← Matrix.mul_smul, hζat y u hu, Matrix.mul_zero]
    rw [eq_map_lift v _ hat, Matrix.map_mul, hζc]
    simp [ζ, f, L, mulLeft, sv]

end GlobalTheory.InertLagParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureEqRelIndexSmulStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMeasure_eq_relIndex_smul : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J J₀ : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ μ₀ : Measure (GA D V)), ι.range = GfC V → J ≤ J₀ → J.relIndex J₀ ≠ 0 →
  IsOpenCompactLevel V K → IsOpenCompactLevel V K₀ → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → (∀ x, Lev.finE V (ι x) ∈ K₀ ↔ x ∈ J₀) →
  Lev.IsMeasLevDef V K μ → Lev.IsMeasLevDef V K₀ μ₀ → μ = (J.relIndex J₀ : ENNReal) • μ₀ := by
  first | exact @GlobalTheory.LevelIndexMeasure.measure_eq_relIndex_smul | exact GlobalTheory.LevelIndexMeasure.measure_eq_relIndex_smul | (intros; apply GlobalTheory.LevelIndexMeasure.measure_eq_relIndex_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BoxSpan

theorem boxFun_mem_SB' {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem schr_boxFun {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ]
    [Fintype κ'] (w : (κ ⊕ κ' → R) × (κ ⊕ κ' → R)) (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    schr ψ w (boxFun φ₁ φ₂) = boxFun (schr ψ (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl) φ₁)
      (schr ψ (w.1 ∘ Sum.inr, w.2 ∘ Sum.inr) φ₂) := by
  funext x
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Function.comp_apply, Pi.add_apply]
  rw [show (∑ i, x (Sum.inl i) * w.2 (Sum.inl i)) + (∑ i, x (Sum.inr i) * w.2 (Sum.inr i)) +
      ⅟(2 : R) * ((∑ i, w.1 (Sum.inl i) * w.2 (Sum.inl i)) + (∑ i, w.1 (Sum.inr i) * w.2 (Sum.inr i))) =
      ((∑ i, x (Sum.inl i) * w.2 (Sum.inl i)) + ⅟(2 : R) * (∑ i, w.1 (Sum.inl i) * w.2 (Sum.inl i))) +
      ((∑ i, x (Sum.inr i) * w.2 (Sum.inr i)) + ⅟(2 : R) * (∑ i, w.1 (Sum.inr i) * w.2 (Sum.inr i))) by ring,
    AddChar.map_add_eq_mul]
  rw [show (x + w.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 ∘ Sum.inl from rfl,
    show (x + w.1) ∘ Sum.inr = x ∘ Sum.inr + w.1 ∘ Sum.inr from rfl]
  ring

end GlobalTheory.BoxSpan

open GlobalTheory.BoxSpan in

theorem GlobalTheory.BoxSpan.boxSpan_ker : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ κ' : Type) [Fintype κ] [Fintype κ'] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ Λ : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), Λ (boxFun φ₁ φ₂) = 0) → ∀ Φ ∈ SB (κ ⊕ κ' → Fv F v), Λ Φ = 0 := by
  intro F _ _ v κ κ' _ _ ψ hψ h1 Λ hΛ Φ hΦ
  classical
  let N : Submodule ℂ ((κ ⊕ κ' → Fv F v) → ℂ) := Submodule.span ℂ
    {f | ∃ φ₁ ∈ SB (κ → Fv F v), ∃ φ₂ ∈ SB (κ' → Fv F v), f = boxFun φ₁ φ₂}
  have hN : N ≤ SB (κ ⊕ κ' → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact boxFun_mem_SB' h₁ h₂
  have hS : ∀ w, ∀ φ ∈ N, schr ψ w φ ∈ N := by
    intro w
    let Lw : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → Fv F v) → ℂ) :=
      { toFun := schr ψ w
        map_add' := fun f g => by funext x; simp [schr, mul_add]
        map_smul' := fun c f => by funext x; simp [schr]; ring }
    have : N ≤ N.comap Lw := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
      show schr ψ w (boxFun φ₁ φ₂) ∈ N
      rw [schr_boxFun]
      exact Submodule.subset_span ⟨_, GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₁, _,
        GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₂, rfl⟩
    exact fun φ hφ => this hφ
  let i₁ := Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ)
  let i₂ := Set.indicator {x : κ' → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ' → Fv F v) → ℂ)
  have h0 : boxFun i₁ i₂ ∈ N := Submodule.subset_span
    ⟨i₁, GlobalTheory.StdVacuum.indicator_mem_SB v, i₂, GlobalTheory.StdVacuum.indicator_mem_SB v, rfl⟩
  have hne : boxFun i₁ i₂ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [boxFun, i₁, i₂, Set.indicator, zero_mem] at this
  have hall := GlobalTheory.SchrIrred.schr_irreducible v ψ hψ h1 N hN hS _ h0 hne
  have hk : N ≤ LinearMap.ker Λ := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact hΛ φ₁ h₁ φ₂ h₂
  rw [← hall] at hΦ
  exact hk hΦ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearHomKillsTorsionOfWeilPairingDivisibleStatement
section
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearHom_kills_torsion_of_weilPairing_divisible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (ψ : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ f : (X.A true).t.G ⟶ X.B.t.G, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      ∃ r : 𝓞 E, GlobalTheory.CM.WeilEq X.B.t.PP.L f ψ (X.A true).t.PP.L ((X.A true).t.act.act ((n : 𝓞 E) * r)) (𝟙 _)
        (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) →
    ∀ u : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, u ^ n = 1 → u ≫ ψ = 1 := by
  first | exact @GlobalTheory.FlatCM.TorsKill.kill | exact GlobalTheory.FlatCM.TorsKill.kill | (intros; apply GlobalTheory.FlatCM.TorsKill.kill <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqLatticeModelRepFundamentalDomainStatement
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_sq_latticeModelRep_fundamentalDomain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f,
            ∫⁻ w in 𝓕, ‖(Om p f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.FinLatUnitF.lintegral_sq_Om | exact GlobalTheory.FinLatUnitF.lintegral_sq_Om | (intros; apply GlobalTheory.FinLatUnitF.lintegral_sq_Om <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValueStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_idempotent_character_value : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {a' d : ℕ} (J : Matrix (Fin a') (Fin a') (AE F E)) (v : Pl F) (t : E →ₐ[F] Fv F v) (f : AE F E),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl J),
      ((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    At (evFin F v) (((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) ∧
    ∀ (u₁ u₂ : Matrix (Fin d) (Fin a') (AE F E)), At (evFin F v) u₁ → At (evFin F v) u₂ →
      (u₁.map (piW t) = 0 → u₂.map (piW t) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (-u₂) (-u₁)) ∧
      (u₁.map (piW (t.comp σ)) = 0 → u₂.map (piW (t.comp σ)) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols u₂ u₁) := by
  first | exact @GlobalTheory.SwapAtPlace.swap_at_acts | exact GlobalTheory.SwapAtPlace.swap_at_acts | (intros; apply GlobalTheory.SwapAtPlace.swap_at_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorLeftPartialPureStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_operator_left_partial_pure : ∀ {F : Type} [Field F] [NumberField F] {κ κ₁ κ' : Type} [Fintype κ] [Fintype κ₁] [Fintype κ'] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ), IsLocOp e → ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ₁ ⊕ κ'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ₁ ⊕ κ' → Af F), ∀ f : SInf F (κ ⊕ κ'), partL e (pureA F f g) = pureA F (P f) g₁ := by
  first | exact @GlobalTheory.DblEval.PartLStr.exists_partL_pureA | exact GlobalTheory.DblEval.PartLStr.exists_partL_pureA | (intros; apply GlobalTheory.DblEval.PartLStr.exists_partL_pureA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalVacuumEigenLatticeStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_vacuum_eigen_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → ∀ (v : Pl F) (t : Matrix (Fin n) (Fin d) (AE F E) → ℂ),
    (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) (M.vac v) = t γ • M.vac v) →
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) φ = t γ • φ) →
      ∃ a : ℂ, φ = a • M.vac v := by
  first | exact @GlobalTheory.VacEigenLine.eigen_line | exact GlobalTheory.VacEigenLine.eigen_line | (intros; apply GlobalTheory.VacEigenLine.eigen_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialRightPreservesL2NormStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_right_preserves_l2_norm : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)),
    (∀ μ : @Measure (κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ φ ∈ schA F κ', ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ Φ ∈ schA F (κ ⊕ κ'), partR T Φ ∈ schA F (κ ⊕ κ')) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partR T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.DblEval.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA | exact GlobalTheory.DblEval.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA | (intros; apply GlobalTheory.DblEval.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA <;> assumption)
end

