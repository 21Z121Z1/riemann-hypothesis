import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicPointInfiniteMatricesEqOneOfFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}

def conjJAt (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) : X.Vpi u →ₗ[ℂ] ℂ where
  toFun η := star (tr.J η z)
  map_add' η η' := by simp [map_add]
  map_smul' c η := by simp [map_smulₛₗ]

def rieszJ (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) : X.Vpi u :=
  (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap (conjJAt tr z))

theorem inner_rieszJ (tr : Formalism.L2.SG.ColDict.Transport X u F) (z : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) (η : X.Vpi u) :
    ⟪η, rieszJ tr z⟫_ℂ = tr.J η z := by
  rw [← inner_conj_symm]
  simp [rieszJ, conjJAt]

variable (X) in

def RepM (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (h : X.B.I.Gf) (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)) : Prop :=
  ∀ j, X.B.I.fmat h *ᵥ Formalism.L2.SG.ColDict.qA X wt j = ∑ i, ιA.symm (M i j) • Formalism.L2.SG.ColDict.qA X wt i

end GlobalTheory.Core.Mi

end

namespace GlobalTheory.Core.Mi

section Helpers

variable {D : D7}

theorem unitaryAdelicPointFiniteMatrix_base_space_mul (a b : GA D (D.sp.X 0)) :
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a * b) =
      GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a *
        GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) b := by
  unfold GlobalTheory.AdForm.finM Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul, Matrix.map_mul]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem unitaryAdelicPointFiniteMatrix_base_space_one : GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (1 : GA D (D.sp.X 0)) = 1 := by
  unfold GlobalTheory.AdForm.finM Formalism.L2.Theta.mt
  simp [Matrix.reindex_apply]

theorem unitaryAdelicPointInfiniteMatrices_base_space_mul (θ : InfFam D) (a b : GA D (D.sp.X 0)) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (a * b) τ =
      GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ *
        GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) b τ := by
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = M.map ((θ τ).comp (infPart D)) := fun M => rfl
  rw [e, e, e, map_mul, Units.val_mul, Matrix.map_mul]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem unitaryAdelicPointInfiniteMatrices_base_space_one (θ : InfFam D) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) (1 : GA D (D.sp.X 0)) τ = 1 := by
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = M.map ((θ τ).comp (infPart D)) := fun M => rfl
  rw [e, map_one, Units.val_one]
  simp [Matrix.reindex_apply]

theorem unitaryAdelicPointInfiniteMatrices_eq_one_of_finite (θ : InfFam D) (a : GA D (D.sp.X 0)) (ha : a ∈ GfC (D.sp.X 0)) (τ : D.what₂.Tau) :
    GlobalTheory.AdForm.infM θ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a τ = 1 := by
  have h1 : Formalism.L2.Theta.infHom (D.sp.X 0) a = 1 := ha
  unfold Formalism.L2.Theta.infHom at h1
  unfold GlobalTheory.AdForm.infM Formalism.L2.Theta.mt compAt
  have h2 := congrArg (fun x : GL (Fin (D.sp.X 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => ((x.1).map (θ τ))) h1
  simp only [MonoidHom.comp_apply, Units.val_one] at h2
  have e : ∀ M : Matrix (Fin (D.sp.X 0).rank) (Fin (D.sp.X 0).rank) (AE D),
      M.map (fun a => θ τ (infPart D a)) = (M.map (infPart D)).map (θ τ) := fun M => by ext; rfl
  rw [e]
  have h3 : ((Formalism.L2.Theta.matHom (D.sp.X 0)) a).1.map (infPart D) =
      ((Formalism.UG.bc (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom)
        ((Formalism.L2.Theta.matHom (D.sp.X 0)) a) : GL _ _).1 := rfl
  rw [h3, h2]
  simp [Matrix.reindex_apply]

end Helpers

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

theorem toH_mul {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D}
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) (a b : GA D A) :
    B.toH (a * b) = B.toH a * B.toH b := by
  unfold SBes.toH
  ext <;> simp [map_mul]

theorem RepM_cancel {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {wt : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {ιA : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F}
    {h k : X.B.I.Gf} {A M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (GlobalTheory.AdForm.EF D)}
    (hA : RepM X wt ιA h A) (hAM : RepM X wt ιA (h * k) (A * M)) : RepM X wt ιA k M := by
  intro j
  have hmul : X.B.I.fmat (h * k) = X.B.I.fmat h * X.B.I.fmat k := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have hinv : X.B.I.fmat h⁻¹ * X.B.I.fmat h = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : X.B.I.fmat h *ᵥ (X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j) =
      X.B.I.fmat h *ᵥ (∑ l, ιA.symm (M l j) • Formalism.L2.SG.ColDict.qA X wt l) := by
    rw [Matrix.mulVec_mulVec, ← hmul, hAM j, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hA, Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hA l, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]
  calc X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j
      = X.B.I.fmat h⁻¹ *ᵥ (X.B.I.fmat h *ᵥ (X.B.I.fmat k *ᵥ Formalism.L2.SG.ColDict.qA X wt j)) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = X.B.I.fmat h⁻¹ *ᵥ (X.B.I.fmat h *ᵥ (∑ l, ιA.symm (M l j) • Formalism.L2.SG.ColDict.qA X wt l)) := by rw [key]
    _ = _ := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

theorem span_rieszJ {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (tr : Formalism.L2.SG.ColDict.Transport X u F) :
    Submodule.span ℂ (Set.range fun y => rieszJ tr (F.val0.eY y)) = ⊤ := by
  obtain ⟨c, -⟩ := F.cls0.y_bij.2 (Quotient.mk'' 1)
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro η hη
  apply tr.J_injective c
  rw [map_zero]
  funext z
  obtain ⟨y, rfl⟩ := F.val0.eY.surjective z
  rw [← inner_rieszJ]
  exact (Submodule.mem_orthogonal' _ _).1 hη _ (Submodule.subset_span ⟨y, rfl⟩)

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi

theorem colDictL_eY_symm {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {F : Formalism.L2.Forms.Forms0 D u}
    (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (c : (D.mem u).C.cls 0)
    (w : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)) :
    Formalism.L2.SG.ColDict.colDictL X tr hK T c (F.val0.eY.symm w) = tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) w := by
  have : Formalism.L2.SG.ColDict.colDictL X tr hK T c (F.val0.eY.symm w) =
      tr.J (Formalism.L2.SG.ColDict.shP X u T.1 (tr.hc c)) (F.val0.eY (F.val0.eY.symm w)) := rfl
  rw [this, Equiv.apply_symm_apply]

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.UpMem
variable {D : D7}
open GlobalTheory.FinPl

theorem smul_mem_latMul (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) (P : Pl D → Prop) (w : AE D)
    (hw : finPart D w ∈ intAE D) : ∀ y ∈ latMul S 𝔞 L P, w • y ∈ latMul S 𝔞 L P := by
  let Ψ : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) := AddMonoidHom.mk' (fun u => w • u) fun x y => smul_add w x y
  have main : latMul S 𝔞 L P ≤ (latMul S 𝔞 L P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, x, hx, rfl⟩
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) := AddMonoidHom.mk'
      (fun y => fun i => GlobalTheory.LatticeStable.liftMul D (α ⊗ₜ[D.host.F] (a * x i)) y)
      fun y y' => funext fun i => (GlobalTheory.LatticeStable.liftMul D _).map_add y y'
    have hle : intAE D ≤ (latMul S 𝔞 L P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨β, hβ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun v hv => ?_, a, ha, o • x, L.smul_mem o hx, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · rw [map_mul, hP v hv, mul_zero]
      · funext i
        change GlobalTheory.LatticeStable.liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] _)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
          show algebraMap _ _ o = (o : D.host.E) from rfl]
        congr 1
        ring
    have e : Ψ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) = Φ (finPart D w) :=
      funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D w α _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact fun u hu => main hu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finPart_e_int (q : SplitPt D k) : finPart D q.e ∈ intAE D := by
  have h := (q.int_iff 1).1 (one_mem _)
  have h1 : q.sec 1 = q.e := by
    have := q.sec_pr 1
    rwa [map_one, mul_one] at this
  rwa [h1] at h

theorem e_mul_mem_latV (q : SplitPt D k) (S : HSp D) (L : Lat S) {s : Fin S.rank → D.host.E} (hs : s ∈ L) :
    (fun j => q.e * incA D (s j)) ∈ latV S L (· = q.v) := by
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, hsum⟩ := q.above
  have hα : α ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have hg : (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s j)) ∈ latV S L (· = q.v) :=
    AddSubgroup.subset_closure ⟨α, hα, fun u hu => h0 u hu, 1, rfl, s, hs, rfl⟩
  have he : q.e • (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s j)) ∈ latV S L (· = q.v) :=
    smul_mem_latMul S {1} L (· = q.v) q.e (finPart_e_int q) _ hg
  convert he using 1
  funext j
  have hee : q.e * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = q.e := by
    rw [← hsum, mul_add, q.split.1, q.split.2.1, add_zero]
  rw [Pi.smul_apply, smul_eq_mul, one_mul]
  have : pairA D.host.F 0 α ⊗ₜ[D.host.F] s j = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * incA D (s j) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change _ = (_ ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] s j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this, ← mul_assoc, hee]

end GlobalTheory.UpMem

namespace GlobalTheory.UpMem
variable {D : D7}
open GlobalTheory.FinPl

theorem rankOne_mem_latO (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop) {s : Fin S.rank → D.host.E}
    (hs : s ∈ LS) {y : Fin T.rank → AE D} (hy : y ∈ latA T LT P) :
    (Matrix.of fun i j => y i * incA D (∑ l, star (s l) * S.gram l j) : WO S T) ∈
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P := by
  let Φ : (Fin T.rank → AE D) →+ WO S T := AddMonoidHom.mk'
    (fun y => Matrix.of fun i j => y i * incA D (∑ l, star (s l) * S.gram l j))
    fun y y' => Matrix.ext fun i j => add_mul (y i) (y' i) _
  have main : latA T LT P ≤ (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩
    ext i j
    change (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  exact main hy

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul (q : SplitPt D k) (a : k) (b : AE D) : q.sec a * b = q.sec (a * q.pr b) := by
  have h1 : q.e * q.sec a = q.sec a := by rw [← q.sec_pr, q.pr_sec]
  calc q.sec a * b = q.e * (q.sec a * b) := by rw [← mul_assoc, h1]
    _ = q.sec (q.pr (q.sec a * b)) := (q.sec_pr _).symm
    _ = q.sec (a * q.pr b) := by rw [map_mul, q.pr_sec]

end GlobalTheory.UpMem

namespace GlobalTheory.UpMem
open GlobalTheory.FinPl

theorem up_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → (ofSplit q).up FS FT x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hS hT hFS hFT x hx
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S LS hS
  set u := (ofSplit q).up FS FT x with hu_def
  let z : Fin n → Y' → k := fun c => FS.γ *ᵥ (fun m => q.pr (incA D (s c m)))
  let y : Fin n → Fin T.rank → AE D := fun c i => ∑ m, u i m * incA D (s c m)
  have hz : ∀ c r, z c r ∈ 𝒪[k] := by
    intro c
    refine (hFS (z c)).2 ?_
    have : (fun i => q.sec ((FS.β *ᵥ z c) i)) = fun j => q.e * incA D (s c j) := by
      funext j
      simp only [z, Matrix.mulVec_mulVec, FS.βγ, Matrix.one_mulVec]
      exact q.sec_pr _
    rw [this]
    exact e_mul_mem_latV q S LS (hs c).1
  have hy : ∀ c, y c ∈ latA T LT (· = q.v) := by
    intro c
    rw [hU.2 T LT]
    have hint : ∀ r, (x *ᵥ z c) r ∈ 𝒪[k] := fun r =>
      Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hx r m) (hz c m)
    convert (hFT (x *ᵥ z c)).1 hint using 1
    funext i
    change ∑ m, q.sec ((FT.β * x * FS.γ) i m) * incA D (s c m) = _
    simp_rw [sec_mul]
    rw [← map_sum]
    congr 1
    simp only [z, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc]
    rfl
  have hdec : u = ∑ c, (Matrix.of fun i j => y c i * incA D (∑ l, star (s' c l) * S.gram l j) : WO S T) := by
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.of_apply, y, Finset.sum_mul]
    rw [Finset.sum_comm]
    have key : ∀ m, ∑ c, u i m * incA D (s c m) * incA D (∑ l, star (s' c l) * S.gram l j) =
        u i m * incA D (if m = j then 1 else 0) := by
      intro m
      rw [← hss m j, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, mul_assoc]
    rw [Finset.sum_congr rfl fun m _ => key m]
    simp [apply_ite]
  rw [hdec]
  exact sum_mem fun c _ => rankOne_mem_latO S T LS LT _ (hs c).2 (hy c)

end GlobalTheory.UpMem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunctionStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_residue_ne_zero_of_simple_pole_lift_L_function : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ (D : D7) (S : Finset (FinPl D)) (r t : ℕ) (c par : GlobalTheory.LFun.Fam D.host.E) (χ : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (S : Set (FinPl D)) r t c par (GlobalTheory.LFun.val (F := D.host.F) χ) (GlobalTheory.LFun.val (F := D.host.F) χ) → ∀ (a b : ℕ) (Z : ℂ → ℂ) (C z : ℂ), C ≠ 0 → EqRight Z (fun s => GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / GlobalTheory.LFun.dSfun D.host.E (S : Set (FinPl D)) a b s * C) → CoeffAt Z ((t : ℂ) / 2) (-1) z → z ≠ 0 := by
  first | exact @GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole | exact GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole | (intros; apply GlobalTheory.Core.Rk.Exh.residue_ne_zero_of_simplePole <;> assumption)
end

