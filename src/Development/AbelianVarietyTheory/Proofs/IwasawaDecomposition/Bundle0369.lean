import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgWeightFWeightTensorDualRepOfEmbeddings
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AlgWtF

open Formalism.L2.DIV
open scoped Matrix

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

theorem awf_eval_aeval {σ₁ σ₂ : Type} (f : σ₁ → MvPolynomial σ₂ K) (d : σ₂ → K) (P : MvPolynomial σ₁ K) :
    MvPolynomial.eval d (MvPolynomial.aeval f P) = MvPolynomial.eval (fun x => MvPolynomial.eval d (f x)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

def awfPt (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* K) × Fin n × Fin n → K := fun p => p.1 (γ₀ p.2.1 p.2.2)

def awfLin {κ : Type} [Fintype κ] (e : Module.Basis κ ℚ L) (p : (L →+* K) × Fin n × Fin n) :
    MvPolynomial (κ × Fin n × Fin n) K :=
  ∑ k : κ, MvPolynomial.C (p.1 (e k)) * MvPolynomial.X (k, p.2.1, p.2.2)

theorem awf_emb_eq {κ : Type} [Fintype κ] (e : Module.Basis κ ℚ L) (σ : L →+* K) (x : L) :
    σ x = ∑ k : κ, σ (e k) * ((e.repr x k : ℚ) : K) := by
  conv_lhs => rw [← e.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast, mul_comm]

theorem isAlgWeightF_of_embPoly {W : Type} [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W)
    (Q : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K)
    (hQ : ∀ γ : GQ L n, LinearMap.toMatrix b b (ρ γ) =
      fun i j => MvPolynomial.eval (awfPt ((ratHom γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (Q i j)) :
    NX.IsAlgWeightF L n K ρ := by
  let e := Module.finBasis ℚ L
  refine ⟨Module.Finite.of_basis b, ι, inferInstance, inferInstance, b, _, inferInstance, e,
    fun i j => MvPolynomial.aeval (awfLin e) (Q i j), ?_⟩
  intro γ γ₀ hm
  obtain rfl := ratHom_eq_of_match γ γ₀ hm
  rw [hQ γ]
  ext i j
  rw [awf_eval_aeval]
  refine congrArg (fun f => MvPolynomial.eval f (Q i j)) (funext fun p => ?_)
  simp only [awfLin, awfPt, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact awf_emb_eq e p.1 _

end Gen

section Poly

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K]

def awfUniv : Pol K ι n →ₐ[K] MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K) :=
  MvPolynomial.aeval fun v => ∑ b : Fin n, MvPolynomial.C (MvPolynomial.X (v.1, b, v.2.1)) * MvPolynomial.X (v.1, b, v.2.2)

theorem awfUniv_map (M : ι → Matrix (Fin n) (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map (MvPolynomial.eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (awfUniv F) =
      Formalism.GradedWeylDivisibility.blockAct K (fun τ => (M τ)ᵀ) F := by
  have h : (MvPolynomial.map (MvPolynomial.eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2)).comp
      (awfUniv (K := K) (ι := ι) (n := n)).toRingHom = (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (M τ)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [awfUniv, Formalism.GradedWeylDivisibility.blockAct]
    · intro v
      simp [awfUniv, Formalism.GradedWeylDivisibility.blockAct, Matrix.transpose_apply]
  exact congrArg (fun f : Pol K ι n →+* Pol K ι n => f F) h

def awfCf (ℓ : Pol K ι n →ₗ[K] K)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K)) : MvPolynomial (ι × Fin n × Fin n) K :=
  ∑ m ∈ Q.support, MvPolynomial.coeff m Q * MvPolynomial.C (ℓ (MvPolynomial.monomial m 1))

theorem awfCf_eval (ℓ : Pol K ι n →ₗ[K] K) (y : ι × Fin n × Fin n → K)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K)) :
    MvPolynomial.eval y (awfCf ℓ Q) = ℓ (MvPolynomial.map (MvPolynomial.eval y) Q) := by
  conv_rhs => rw [Q.as_sum]
  rw [map_sum, map_sum, awfCf, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    show MvPolynomial.monomial m (MvPolynomial.eval y (MvPolynomial.coeff m Q)) =
        MvPolynomial.eval y (MvPolynomial.coeff m Q) • (MvPolynomial.monomial m 1 : Pol K ι n) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

def awfCoord (lam : ι → DomWeight n) (i : VVIdx lam) : Pol K ι n →ₗ[K] K :=
  (LinearMap.exists_extend ((bVV K lam).coord i)).choose

theorem awfCoord_spec (lam : ι → DomWeight n) (i : VVIdx lam) (F : VV K lam) :
    awfCoord lam i (F : Pol K ι n) = (bVV K lam).repr F i := by
  have h := (LinearMap.exists_extend ((bVV K lam).coord i)).choose_spec
  have := LinearMap.congr_fun h F
  simpa [awfCoord, Module.Basis.coord_apply] using this

def awfCoef (lam : ι → DomWeight n) (i j : VVIdx lam) : MvPolynomial (ι × Fin n × Fin n) K :=
  awfCf (awfCoord lam i) (awfUniv (bVVfun K lam j))

theorem awfCoef_eval (lam : ι → DomWeight n) (M : ι → Matrix (Fin n) (Fin n) K) (i j : VVIdx lam) :
    MvPolynomial.eval (fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (awfCoef lam i j) =
      awfCoord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (M τ)ᵀ) (bVVfun K lam j)) := by
  rw [awfCoef, awfCf_eval, awfUniv_map]

end Poly

section Alg

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

def awfDetP (σ : L →+* K) : MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  (Matrix.of fun a b => (MvPolynomial.X (σ, a, b) : MvPolynomial ((L →+* K) × Fin n × Fin n) K)).det

theorem awfDetP_eval (σ : L →+* K) (γ₀ : Matrix (Fin n) (Fin n) L) :
    MvPolynomial.eval (awfPt γ₀) (awfDetP σ) = σ γ₀.det := by
  rw [awfDetP, RingHom.map_det, RingHom.map_det]
  congr 1
  ext a b
  simp [awfPt]

theorem awf_det_conj (σ : L →+* K) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    (σ.comp (IsCMField.complexConj L : L →+* L)) (γ₀ : Matrix (Fin n) (Fin n) L).det =
      (σ (γ₀ : Matrix (Fin n) (Fin n) L).det)⁻¹ := by
  have h1 : ((γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀).det = 1 := by
    rw [show (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 from hγ,
      Matrix.det_one]
  have h2 : ((γ₀ : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L : L →+* L)).det =
      (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    rw [RingHom.map_det]
    rfl
  rw [Matrix.det_mul, conjT, Matrix.det_transpose, h2] at h1
  apply eq_inv_of_mul_eq_one_right
  rw [RingHom.comp_apply, ← map_mul, h1, map_one]

theorem awf_inv_entry (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) (k l : Fin n) :
    ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k l =
      (IsCMField.complexConj L : L →+* L) ((γ₀ : Matrix (Fin n) (Fin n) L) l k) := by
  have h1 : ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
    Units.inv_eq_of_mul_eq_one_right hγ
  rw [h1]
  rfl

def awfTwP (emb : ι → L →+* K) (lam : ι → DomWeight n) : MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  ∏ τ, if 0 ≤ (lam τ).detShift then awfDetP (emb τ) ^ (lam τ).detShift.toNat
    else awfDetP ((emb τ).comp (IsCMField.complexConj L : L →+* L)) ^ (-(lam τ).detShift).toNat

theorem awfTwP_eval (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    MvPolynomial.eval (awfPt (γ₀ : Matrix (Fin n) (Fin n) L)) (awfTwP emb lam) = detTwK lam (embGLF emb γ₀) := by
  simp only [awfTwP, detTwK, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : ((Matrix.GeneralLinearGroup.det (embGLF emb γ₀ τ) : Kˣ) : K) = emb τ (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  rw [detPow, Units.val_zpow_eq_zpow_val, hd]
  split_ifs with h
  · rw [map_pow, awfDetP_eval, ← zpow_natCast, Int.toNat_of_nonneg h]
  · rw [map_pow, awfDetP_eval, awf_det_conj _ _ hγ, ← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow', neg_neg]

def awfTenP (emb : ι → L →+* K) (lam : ι → DomWeight n) (i j : VVIdx lam) :
    MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  awfTwP emb lam * MvPolynomial.aeval
    (fun y : ι × Fin n × Fin n => (MvPolynomial.X (emb y.1, y.2.1, y.2.2) : MvPolynomial ((L →+* K) × Fin n × Fin n) K))
    (awfCoef (K := K) lam i j)

theorem awfTenP_eval (emb : ι → L →+* K) (lam : ι → DomWeight n) (i j : VVIdx lam) (y : (L →+* K) × Fin n × Fin n → K) :
    MvPolynomial.eval y (awfTenP emb lam i j) = MvPolynomial.eval y (awfTwP emb lam) *
      awfCoord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (Matrix.of fun a b => y (emb τ, a, b))ᵀ) (bVVfun K lam j)) := by
  rw [awfTenP, MvPolynomial.eval_mul, awf_eval_aeval, ← awfCoef_eval]
  simp

theorem tenRepF_toMatrix (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ : GQ L n) :
    LinearMap.toMatrix (bVV K lam) (bVV K lam) (tenRepF emb lam γ) =
      fun i j => MvPolynomial.eval (awfPt ((ratHom γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (awfTenP emb lam i j) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, ← awfCoord_spec, awfTenP_eval, awfTwP_eval _ _ _ (ratHom_mem γ)]
  simp only [tenRepF, MonoidHom.comp_apply, rhoK, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_restrict_apply, bVV_coe,
    actP, trAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul]
  congr 2

end Alg

section Dual

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

open Classical in

theorem wtRepF_toMatrix (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ : GQ L n) :
    LinearMap.toMatrix (bVV K lam).dualBasis (bVV K lam).dualBasis (wtRepF emb lam γ) =
      fun i j => MvPolynomial.eval (awfPt ((ratHom γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
        (MvPolynomial.rename (fun p : (L →+* K) × Fin n × Fin n =>
          (p.1.comp (IsCMField.complexConj L : L →+* L), p.2.2, p.2.1)) (awfTenP emb lam j i)) := by
  have e : LinearMap.toMatrix (bVV K lam).dualBasis (bVV K lam).dualBasis (wtRepF emb lam γ) =
      (LinearMap.toMatrix (bVV K lam) (bVV K lam) (tenRepF emb lam γ⁻¹))ᵀ := by
    rw [wtRepF, Representation.dual_apply, LinearMap.toMatrix_transpose]
  rw [e, tenRepF_toMatrix]
  ext i j
  show MvPolynomial.eval (awfPt ((ratHom γ⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (awfTenP emb lam j i) = _
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun f => MvPolynomial.eval f (awfTenP emb lam j i)) (funext fun p => ?_)
  simp only [Function.comp_apply, awfPt, RingHom.comp_apply, map_inv]
  rw [awf_inv_entry _ (ratHom_mem γ)]

end Dual

theorem wtRepF_alg : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), NX.IsAlgWeightF L n K (GlobalTheory.AlgWtF.wtRepF emb lam) := by
  intro L _ _ _ n ι _ K _ emb lam
  classical
  exact isAlgWeightF_of_embPoly _ (bVV K lam).dualBasis _ (wtRepF_toMatrix emb lam)

end GlobalTheory.AlgWtF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelJoinOnV0ThreeStatement
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_join_on_V0_three : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → SchurAll D → (D.sp.Y 0).SigOK → ∀ (S0 : IndefData (A3.side3 F.P0 F.ψ0 (R.toCx3 F).zs)) (p0 : BaseLevelRowSide D) (C : ColData (F.Dc (R.toCx3 F).zs) (F.Sp (R.toCx3 F).zs) ((R.toCx3 F).data F.cr true)) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin ((F.Dc (R.toCx3 F).zs).a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 (F.Dc (R.toCx3 F).zs)), DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → (∀ (u : D.what₂.Word) (x : Fin ((F.Dc (R.toCx3 F).zs).a (I.wU u)) → D.what₂.LL) (y : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV A3.A.μ0) → D.what₂.LL), D.what₂.embLL ((F.Dc (R.toCx3 F).zs).Pt (I.wU u) A3.A.μ0 x y) = D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) → ∃ (Rd : Read D (R.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0)) (M : Seam Rd F.cr), HEq Rd.wU I.wU ∧ M.ChainTie ∧ M.GoodPartHasComplexCoordinates ∧ M.RowTie (F.eV (R.toCx3 F).zs) ∧ M.ColNorm ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ ∧ ∀ (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (F.Dc (R.toCx3 F).zs).Mem → D.what₂.Word) (bR : ∀ x, Fin ((F.Dc (R.toCx3 F).zs).a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (I.wU u) = u) → F.Sp (R.toCx3 F).zs = spOf (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (I.wU u) i) (D.eMu u (D.jN u (I.eNu u (Pi.single i 1))))) → ∀ (t : GA D (D.sp.Y 0)) (c : ℝ), EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ), HEq sEE sEEc → κS ≠ 0 → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c ⟨R.HE.e (Tw.out x), hx⟩)) → ∀ (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, eE (D.jEE (I.eRR y)) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y))) → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St Gd) (v₀ : (R.MY 0).Vec) (a : ℂ), (∀ x, ((j x : EEC St Gd) : L2X St) =ᵐ[muX St] fun g => a * ev (R.MY 0) v₀ (R.HE.e (eE x)) ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm g * t)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (x : D.what₂.EE) (φ : D.what₂.Mu u) (T' : Cu St u hK), colDictL St (pw u).Tr hK T' = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR x), (F.fc (R.toCx3 F).zs).Sp.Pu (Rd.wU u) (cjv (twAt D.what₂.embLL A3.A.v0) (M.cφ u φ))⟫_ℂ = cj (twAt D.what₂.embLL A3.A.v0) (κ * ⟪((conjHH St Gd (j x) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T'⟫_ℂ) := by
  first | exact @GlobalTheory.Mem.SJ.KernelJoin.kernelJoin_onV0 | exact GlobalTheory.Mem.SJ.KernelJoin.kernelJoin_onV0 | (intros; apply GlobalTheory.Mem.SJ.KernelJoin.kernelJoin_onV0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.WtComb

theorem orderEmb_add_le {n : ℕ} (e : Fin n ↪o ℤ) :
    ∀ (k : ℕ) (a b : Fin n), (b : ℕ) = (a : ℕ) + k → e a + (k : ℤ) ≤ e b := by
  intro k
  induction k with
  | zero =>
    intro a b hb
    have : a = b := Fin.ext (by omega)
    subst this; simp
  | succ k ih =>
    intro a b hb
    have hk : (a : ℕ) + k < n := by have := b.2; omega
    have h1 := ih a ⟨(a : ℕ) + k, hk⟩ rfl
    have h2 : e ⟨(a : ℕ) + k, hk⟩ < e b := e.lt_iff_lt.2 (by rw [Fin.lt_def]; simp; omega)
    push_cast; linarith

theorem exists_domWeight_infOf (n : ℕ) (S : Multiset ℂ) (hc : Multiset.card S = n) (hd : S.Nodup)
    (hm : ∀ x ∈ S, ∃ z : ℤ, x = (z : ℂ) + ((n : ℂ) - 1) / 2) :
    ∃ lam : DomWeight n, NG.infOf lam.w = S := by
  classical
  set c : ℂ := ((n : ℂ) - 1) / 2 with hcdef
  let g : ℂ → ℤ := fun x => if h : ∃ z : ℤ, x = (z : ℂ) + c then h.choose else 0
  have hg : ∀ x ∈ S, x = (g x : ℂ) + c := fun x hx => by
    simp only [g, dif_pos (hm x hx)]; exact (hm x hx).choose_spec
  let M : Multiset ℤ := S.map (fun x => -g x)
  have hMd : M.Nodup := hd.map_on (fun x hx y hy hxy => by
    rw [hg x hx, hg y hy]; simp only [neg_inj] at hxy; rw [hxy])
  let T : Finset ℤ := ⟨M, hMd⟩
  have hT : T.card = n := by simp [T, M, hc]
  let e := T.orderEmbOfFin hT
  refine ⟨⟨fun a => -e a + (a : ℕ), ?_⟩, ?_⟩
  · intro a b hab
    have := orderEmb_add_le e ((b : ℕ) - (a : ℕ)) a b (by rw [Fin.le_def] at hab; omega)
    show -e b + ((b : ℕ) : ℤ) ≤ -e a + ((a : ℕ) : ℤ)
    rw [Fin.le_def] at hab
    push_cast [Nat.cast_sub hab] at this
    linarith
  · unfold NG.infOf
    have h1 : (Finset.univ.map e.toEmbedding) = T := Finset.map_orderEmbOfFin_univ T hT
    calc (Finset.univ.val.map fun a : Fin n => ((-e a + ((a : ℕ) : ℤ) : ℤ) : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ))
        = (Finset.univ.val.map fun a : Fin n => e a).map (fun y : ℤ => -(y : ℂ) + c) := by
          rw [Multiset.map_map]
          refine Multiset.map_congr rfl fun a _ => ?_
          simp only [Function.comp, hcdef]; push_cast; ring
      _ = T.val.map (fun y : ℤ => -(y : ℂ) + c) := by rw [← h1]; rfl
      _ = S := by
          show M.map _ = S
          rw [Multiset.map_map]
          conv_rhs => rw [← Multiset.map_id S]
          refine Multiset.map_congr rfl fun x hx => ?_
          simp only [Function.comp, id]
          have h := hg x hx
          push_cast
          linear_combination -1 * h

end GlobalTheory.WtComb

namespace GlobalTheory.WtComb

theorem chain_lt (f : ℕ → ℚ) (N : ℕ) (hs : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i i', i < i' → i' < N → f i' < f i := by
  intro i i' h
  induction i' with
  | zero => omega
  | succ i' ih =>
    intro hN
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · exact lt_trans (hs i' hN) (ih h' (by omega))
    · subst h'; exact hs i hN

theorem chain_le (f : ℕ → ℚ) (N : ℕ) (hs : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i i', i ≤ i' → i' < N → f i' ≤ f i := by
  intro i i' h hN
  rcases Nat.lt_or_eq_of_le h with h' | h'
  · exact (chain_lt f N hs i i' h' hN).le
  · rw [h']

def qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Finset.univ.val.map fun i : Fin (R.k - 1) => h.v i) + (Finset.univ.val.map fun i : Fin R.m => -h.b i) +
  ((Multiset.range R.t).map fun c : ℕ => -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2)

theorem paramV_eq (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ) :
    NG.paramV R h j sh = (qv R h j).map (fun q : ℚ => (q : ℂ) - sh) := by
  unfold NG.paramV qv
  simp only [Multiset.map_add, Multiset.map_map]
  congr 1
  · congr 1
    all_goals refine Multiset.map_congr rfl fun i _ => ?_
    all_goals simp only [Function.comp]; push_cast; try ring
  · refine Multiset.map_congr rfl fun c _ => ?_
    simp only [Function.comp]; push_cast; try ring

theorem card_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : Multiset.card (qv R h j) = R.nV := by
  have := R.m_add_three_le_k
  simp [qv, Ranks.nV, Ranks.r]
  omega

end GlobalTheory.WtComb

namespace GlobalTheory.WtComb

theorem nodup_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : (qv R h j).Nodup := by
  classical
  have hk := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have ht0 : (0 : ℚ) ≤ R.t := by positivity
  let U : ℕ → ℚ := fun i => if hi : i < R.k then h.u ⟨i, hi⟩ else 0
  let V : ℕ → ℚ := fun i => if hi : i < R.k - 1 then h.v ⟨i, hi⟩ else 0
  let B : ℕ → ℚ := fun i => if hi : i < R.m then -h.b ⟨i, hi⟩ else 0
  have hU : ∀ i, i + 1 < R.k → U (i + 1) < U i := by
    intro i hi
    have h1 := h.u_gt_v ⟨i, by omega⟩
    have h2 := h.v_gt_u ⟨i, by omega⟩
    simp only [U, dif_pos hi, dif_pos (show i < R.k by omega)]
    exact lt_trans h2 h1
  have hV : ∀ i, i + 1 < R.k - 1 → V (i + 1) < V i := by
    intro i hi
    have h1 := h.u_gt_v ⟨i + 1, hi⟩
    have h2 := h.v_gt_u ⟨i, by omega⟩
    simp only [V, dif_pos hi, dif_pos (show i < R.k - 1 by omega)]
    exact lt_trans h1 h2
  have hB : ∀ i, i + 1 < R.m → B (i + 1) < B i := by
    intro i hi
    have h1 := h.gap_be ⟨i, by omega⟩
    have h2 := h.gap_eb ⟨i, by omega⟩ hi
    simp only [B, dif_pos hi, dif_pos (show i < R.m by omega)]
    linarith
  have bmono : ∀ i i' : Fin R.m, i.1 ≤ i'.1 → -h.b i' ≤ -h.b i := by
    intro i i' hii
    have := chain_le B R.m hB i.1 i'.1 hii i'.2
    simpa only [B, dif_pos i.2, dif_pos i'.2] using this
  have vgt : ∀ (i : Fin (R.k - 1)) (i' : Fin R.m), -h.b i' < h.v i := by
    intro i i'
    have a1 := h.v_gt_u i
    have a2 := chain_le U R.k hU (i.1 + 1) (R.k - 1) (by omega) (by omega)
    have a3 := h.u_last_gt (by omega) (by omega)
    have a4 := bmono ⟨0, by omega⟩ i' (Nat.zero_le _)
    simp only [U, dif_pos (show R.k - 1 < R.k by omega), dif_pos (show i.1 + 1 < R.k by omega)] at a2
    linarith
  have top : ∀ c : ℕ, -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 < -h.b j := by
    intro c
    have := h.gap_be j
    have hc : (0 : ℚ) ≤ c := by positivity
    linarith
  have bne : ∀ (i : Fin R.m) (c : ℕ), c < R.t → -h.b i ≠ -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro i c hc
    by_cases hij : i.1 ≤ j.1
    · have := bmono i j hij
      have := top c
      intro heq; linarith
    · have hj1 : j.1 + 1 < R.m := by have := i.2; omega
      have a1 := h.gap_eb j hj1
      have a2 := bmono ⟨j.1 + 1, hj1⟩ i (show j.1 + 1 ≤ i.1 by omega)
      have hc' : (c : ℚ) + 1 ≤ R.t := by exact_mod_cast hc
      intro heq; linarith
  have vne : ∀ (i : Fin (R.k - 1)) (c : ℕ), h.v i ≠ -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro i c heq
    have := vgt i j
    have := top c
    linarith
  have vinj : Function.Injective h.v := by
    refine StrictAnti.injective fun a b hab => ?_
    have := chain_lt V (R.k - 1) hV a.1 b.1 hab b.2
    simpa only [V, dif_pos a.2, dif_pos b.2] using this
  have binj : Function.Injective fun i : Fin R.m => -h.b i := by
    refine StrictAnti.injective fun a b hab => ?_
    have := chain_lt B R.m hB a.1 b.1 hab b.2
    simpa only [B, dif_pos a.2, dif_pos b.2] using this
  have rinj : Function.Injective fun c : ℕ => -h.e j + ((R.t : ℚ) - 1 - 2 * c) / 2 := by
    intro c c' hcc
    have : (c : ℚ) = c' := by simp only at hcc; linarith
    exact_mod_cast this
  unfold qv
  refine Multiset.nodup_add.2 ⟨Multiset.nodup_add.2 ⟨Finset.univ.nodup.map vinj, Finset.univ.nodup.map binj, ?_⟩,
    (Multiset.nodup_range _).map rinj, ?_⟩
  · refine Multiset.disjoint_left.2 fun ha hb => ?_
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
    obtain ⟨i', -, hi'⟩ := Multiset.mem_map.1 hb
    have := vgt i i'
    linarith
  · refine Multiset.disjoint_left.2 fun ha hb => ?_
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [Multiset.mem_range] at hc
    rcases Multiset.mem_add.1 ha with ha | ha
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 ha
      exact vne i c hi
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 ha
      exact bne i c hc hi

theorem int_qv (R : Ranks) (h : HCParam R) (j : Fin R.m) : ∀ q ∈ qv R h j, ∃ z : ℤ, q = z := by
  intro q hq
  unfold qv at hq
  rcases Multiset.mem_add.1 hq with hq | hq
  · rcases Multiset.mem_add.1 hq with hq | hq
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hq
      exact h.v_int i
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hq
      obtain ⟨z, hz⟩ := h.b_int i
      exact ⟨-z, by rw [hz]; push_cast; ring⟩
  · obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hq
    obtain ⟨z, hz⟩ := h.e_int j
    obtain ⟨s, hs⟩ := R.t_odd
    refine ⟨-z + s - c, ?_⟩
    rw [hz, hs]; push_cast; ring

theorem paramV_eq_infOf : ∀ (R : Ranks) (h : HCParam R) (j : Fin R.m) (sh : ℂ), (∃ z : ℤ, sh = (z : ℂ) + 1 / 2) →
    ∃ lam : DomWeight R.nV, NG.infOf lam.w = NG.paramV R h j sh := by
  intro R h j sh ⟨z', hz'⟩
  rw [paramV_eq]
  apply exists_domWeight_infOf
  · rw [Multiset.card_map, card_qv]
  · exact (nodup_qv R h j).map (fun a b hab => by simpa using hab)
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨w, rfl⟩ := int_qv R h j q hq
    obtain ⟨a, ha⟩ := R.k_even
    obtain ⟨b, hb⟩ := R.m_even
    obtain ⟨s, hs⟩ := R.t_odd
    have hk := R.m_add_three_le_k
    have hp : R.nV = 2 * (a + b + s) := by simp only [Ranks.nV, Ranks.r]; omega
    refine ⟨w - z' - (a + b + s), ?_⟩
    rw [hz', hp]; push_cast; ring

end GlobalTheory.WtComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftedHeckeOperatorsAtGeneratorsCommuteStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftedHeckeOperators_at_generators_commute : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q), HeckeStdPlain → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) := by
  first | exact @GlobalTheory.HeckeLocCommute.hLC_commute | exact GlobalTheory.HeckeLocCommute.hLC_commute | (intros; apply GlobalTheory.HeckeLocCommute.hLC_commute <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBridgesAtPlacesOverResidueCharOfLargeCoeffStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBridges_at_placesOverResidueChar_of_large_coeff : ∀ (D : D7) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), F0.1 ≤ (X.Kx j w).1 → BrAt X j w := by
  first | exact @GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large | exact GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large | (intros; apply GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationGaloisCharacterContinuousStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisation_galoisCharacter_continuous : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (twC : ∀ j w, D.ntw.O0 (C.twI w) →+* OcC X j w) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) (hP : PsiInt X ψ0), (∀ j w, TwAlgAt C X j w (twC j w)) → (∀ j w, IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om))) → ∀ (i : LocT (base M C hR X hS)) (c : ℕ), Continuous (fun g => ((chiN (base M C hR X hS) C (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i)) i c g : (OOf (base M C hR X hS) i)ˣ) : OOf (base M C hR X hS) i)) := by
  first | exact @GlobalTheory.HeckeLocCont.chiN_continuous | exact GlobalTheory.HeckeLocCont.chiN_continuous | (intros; apply GlobalTheory.HeckeLocCont.chiN_continuous <;> assumption)
end

