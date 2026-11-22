import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0167
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonBorelJacquetOfCuspidalSegmentJacquet
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.SmGL.CuspSegment

def intervals (l d : ℕ) : (Σ _ : Fin l, Fin d) ≃ Fin (l * d) :=
  (Equiv.sigmaEquivProd _ _).trans finProdFinEquiv

theorem intervals_lt {l d : ℕ} {a b : Fin l} {i j : Fin d}
    (h : intervals l d ⟨a, i⟩ < intervals l d ⟨b, j⟩) : a < b ∨ (a = b ∧ i < j) := by
  have key : (i : ℕ) + d * a < j + d * b := by
    simpa [intervals, finProdFinEquiv, Fin.lt_def] using h
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact Or.inl hab
  · exact Or.inr ⟨rfl, Fin.lt_def.2 (by omega)⟩
  · exfalso
    have h1 : (b : ℕ) + 1 ≤ a := hab
    have h2 : d * ((b : ℕ) + 1) ≤ d * a := Nat.mul_le_mul_left d h1
    have hj := j.isLt
    rw [Nat.mul_succ] at h2
    omega

variable {R : Type} [CommRing R]

theorem unipRad_intervals_le (l d : ℕ) : unipRad R (intervals l d) ≤ unipB R (Fin (l * d)) := by
  intro g hg
  obtain ⟨hpar, hdiag⟩ := mem_unipRad.1 hg
  rw [mem_parab] at hpar
  rw [mem_unipB]
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    obtain ⟨⟨b, j⟩, rfl⟩ := (intervals l d).surjective q
    rcases intervals_lt hqp with hba | ⟨rfl, hji⟩
    · exact hpar _ _ (by simpa using hba)
    · rw [hdiag]
      exact Matrix.one_apply_ne hji.ne'
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    rw [hdiag]
    exact Matrix.one_apply_eq i

theorem leviEmb_intervals_mem {l d : ℕ} (g : Levi R fun _ : Fin l => Fin d)
    (hg : ∀ a, g a ∈ unipB R (Fin d)) : leviEmb R (intervals l d) g ∈ unipB R (Fin (l * d)) := by
  rw [mem_unipB]
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    obtain ⟨⟨b, j⟩, rfl⟩ := (intervals l d).surjective q
    rcases intervals_lt hqp with hba | ⟨rfl, hji⟩
    · exact leviEmb_apply_ne _ _ _ hba.ne' _ _
    · rw [leviEmb_apply_same]
      exact ((mem_unipB (R := R)).1 (hg b)).1 i j hji
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    rw [leviEmb_apply_same]
    exact ((mem_unipB (R := R)).1 (hg a)).2 i

theorem twKer_unipB_eq_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} (hd : 1 < d) {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin d) k) W} (hσ : IsCuspidal σ) :
    twKer σ (unipB k (Fin d)) 1 = ⊤ := by
  classical
  obtain ⟨-, hcusp⟩ := hσ

  let e : (Σ _ : Fin d, Fin 1) ≃ Fin d := Equiv.sigmaUnique (Fin d) fun _ => Fin 1
  have hblk : ∀ i, blk e i = i := fun i => rfl
  have hne : unipRad k e ≠ ⊥ := by
    rw [CuspMax.unipRad_ne_bot_iff]
    refine ⟨⟨0, by omega⟩, ⟨1, hd⟩, ?_⟩
    rw [hblk, hblk]
    exact Fin.mk_lt_mk.2 Nat.zero_lt_one
  have hsub : Subsingleton (Jacquet σ (unipRad k e)) := hcusp d (fun _ => 1) e hne
  have hB : Subsingleton (Jacquet σ (unipRad k (points (Fin d)))) :=
    CuspMax.subsingleton_jacquet_of_perm σ (e := e) (e' := points (Fin d)) (Equiv.refl _)
      (fun i j h => h) hsub
  exact Submodule.Quotient.subsingleton_iff.1 hB

private theorem deltaHalf_eq_one_of_unipB {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {l d : ℕ} (g : Levi k fun _ : Fin l => Fin d)
    (hg : ∀ a, g a ∈ unipB k (Fin d)) : deltaHalf k (fun _ : Fin l => Fin d) g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [det_eq_one_of_mem_unipRad (hu := (show g a ∈ unipRad k (points (Fin d)) from hg a)), map_one]

theorem subsingleton_jacquet_unipB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (l d : ℕ) (hl : 0 < l) (hd : 1 < d) (V : Type) [AddCommGroup V]
    [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin d) k) W)
    (π : Representation ℂ (GL (Fin (l * d)) k) V) (hσ : IsCuspidal σ)
    (h : ∀ e : (Σ _ : Fin l, Fin d) ≃ Fin (l * d),
      Nonempty ((jac e π).Equiv (piTensor (segTerm σ l)))) :
    Subsingleton (Jacquet π (unipB k (Fin (l * d)))) := by
  classical
  obtain ⟨φ⟩ := h (intervals l d)
  obtain ⟨a₀⟩ : Nonempty (Fin l) := ⟨⟨0, hl⟩⟩
  set K := twKer π (unipB k (Fin (l * d))) 1 with hK

  have hgen : ∀ u ∈ unipB k (Fin (l * d)), ∀ v : V, π u v - v ∈ K := by
    intro u hu v
    exact Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩

  have hUK : twKer π (unipRad k (intervals l d)) 1 ≤ K := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, v, rfl⟩
    simpa using hgen n (unipRad_intervals_le l d n.2) v
  let P := Submodule.factor hUK
  have hP : ∀ v : V, P (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun v =>
    Submodule.factor_mk hUK v

  have hlevi : ∀ g : Levi k (fun _ : Fin l => Fin d), (∀ a, g a ∈ unipB k (Fin d)) →
      ∀ q, P (jac (intervals l d) π g q) = P q := by
    intro g hg q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [jac_mk, deltaHalf_eq_one_of_unipB g hg, inv_one, Units.val_one, one_smul, hP, hP]
    exact (Submodule.Quotient.eq _).2 (hgen _ (leviEmb_intervals_mem g hg) v)

  have hfwd : ∀ g z, φ (jac (intervals l d) π g z) = piTensor (segTerm σ l) g (φ z) := by
    intro g z
    have := LinearMap.congr_fun (φ.isIntertwining' g) z
    simpa using this
  have hint : ∀ g y, φ.symm (piTensor (segTerm σ l) g y) = jac (intervals l d) π g (φ.symm y) := by
    intro g y
    apply EquivLike.injective φ
    rw [hfwd, Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply]
  let F : (⨂[ℂ] _ : Fin l, W) →ₗ[ℂ] V ⧸ K := P ∘ₗ φ.symm.toLinearMap
  have hFapp : ∀ y, F y = P (φ.symm y) := fun y => rfl
  have hF : ∀ g : Levi k (fun _ : Fin l => Fin d), (∀ a, g a ∈ unipB k (Fin d)) →
      ∀ y, F (piTensor (segTerm σ l) g y) = F y := by
    intro g hg y
    rw [hFapp, hFapp, hint]
    exact hlevi g hg _

  have htop : twKer (segTerm σ l a₀) (unipB k (Fin d)) 1 = ⊤ :=
    twKer_unipB_eq_top hd (LocGL.isCuspidal_twist hσ (LocGL.isSmoothChar_absPow _))
  have htens : ∀ x : Fin l → W, F (PiTensorProduct.tprod ℂ x) = 0 := by
    intro x
    let Lx := (PiTensorProduct.tprod ℂ).toLinearMap x a₀
    have hker : twKer (segTerm σ l a₀) (unipB k (Fin d)) 1 ≤ LinearMap.ker (F ∘ₗ Lx) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      have hg : ∀ a, (Pi.mulSingle a₀ (u : GL (Fin d) k) : Levi k fun _ : Fin l => Fin d) a ∈
          unipB k (Fin d) := by
        intro a
        by_cases ha : a = a₀
        · rw [ha, Pi.mulSingle_eq_same]
          exact u.2
        · rw [Pi.mulSingle_eq_of_ne ha]
          exact one_mem _
      have hact : Lx (segTerm σ l a₀ u v) =
          piTensor (segTerm σ l) (Pi.mulSingle a₀ (u : GL (Fin d) k)) (Lx v) := by
        simp only [Lx, MultilinearMap.toLinearMap_apply, piTensor_tprod]
        congr 1
        funext a
        by_cases ha : a = a₀
        · rw [ha]
          simp
        · simp [ha]
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, MonoidHom.one_apply,
        Units.val_one, one_smul, map_sub, hact, hF _ hg, sub_self]
    have hx : Lx (x a₀) = PiTensorProduct.tprod ℂ x := by
      simp [Lx]
    rw [← hx]
    exact LinearMap.mem_ker.1 (hker (by rw [htop]; exact Submodule.mem_top))
  have hF0 : F = 0 := PiTensorProduct.ext (MultilinearMap.ext fun x => by simpa using htens x)

  have hv : ∀ v : V, (Submodule.Quotient.mk v : V ⧸ K) = 0 := by
    intro v
    rw [← hP v]
    have hPF : P (Submodule.Quotient.mk v) = F (φ (Submodule.Quotient.mk v)) := by
      rw [hFapp, Representation.Equiv.symm_apply_apply]
    rw [hPF, hF0, LinearMap.zero_apply]
  refine ⟨fun a b => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact (hv v).trans (hv w).symm

end GlobalTheory.SmGL.CuspSegment
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceInverseGramConjSmulEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan

variable {D : D7}

theorem frameMatrix_mul_frameMatrixInv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : frP S b * frPinv S b = 1 :=
  Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem frPinv_mul_frP (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : frPinv S b * frP S b = 1 :=
  Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem isoPair_re (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    GlobalTheory.VolTransport.IsoPair (D.sp.cm.sig : D.host.E →+* D.host.E) (reS S b).gram S.gram (frP S b) (frPinv S b) := by
  refine ⟨frameMatrix_mul_frameMatrixInv S b, frPinv_mul_frP S b, ?_, ?_⟩
  · have := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm (reS S b) S LinearMap.id (fun x y => rfl)
    have e : (LinearMap.toMatrix (reS S b).frame S.frame) LinearMap.id = frP S b :=
      LinearMap.toMatrix_id_eq_basis_toMatrix b S.frame
    rw [← e]; exact this
  · have := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat_isom D.sp.cm S (reS S b) LinearMap.id (fun x y => rfl)
    have e : (LinearMap.toMatrix S.frame (reS S b).frame) LinearMap.id = frPinv S b :=
      LinearMap.toMatrix_id_eq_basis_toMatrix S.frame b
    rw [← e]; exact this

def reGrp (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : GA D (reS S b) ≃* GA D S :=
  GlobalTheory.VolTransport.conjA (isoPair_re S b)

theorem mt_reGrp (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (h : GA D (reS S b)) :
    mt S (reGrp S b h) = HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D))
      (β := Matrix (Fin S.rank) (Fin S.rank) (AE D)) (γ := Matrix (Fin S.rank) (Fin S.rank) (AE D))
      (HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D)) (β := Matrix (Fin S.rank) (Fin S.rank) (AE D))
        (γ := Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((frP S b).map (incA D)) (mt (reS S b) h))
      ((frPinv S b).map (incA D)) :=
  GlobalTheory.VolTransport.conjA_mat (isoPair_re S b) h

theorem finHom_eq (V : HSp D) (g : GA D V) :
    ((finHom V g : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) _) = finMat D.sp.cm.sig V.gram g := rfl

theorem reW_continuous (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Continuous (reW S T b) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  unfold reW
  exact continuous_id.matrix_mul continuous_const

set_option synthInstance.maxHeartbeats 200000 in
theorem mul_mul_cancel {m n : ℕ} (x : Matrix (Fin m) (Fin n) (AE D)) (A B : Matrix (Fin n) (Fin n) (AE D))
    (h : A * B = 1) : x * A * B = x := by
  rw [Matrix.mul_assoc, h, Matrix.mul_one]

variable (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

def reWinv (x : WO S T) : WO (reS S b) T :=
  HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frP S b).map (incA D))

theorem frPinv_frP_A : HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((frPinv S b).map (incA D))
    ((frP S b).map (incA D)) = 1 := by
  rw [← Matrix.map_mul, frPinv_mul_frP, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_frameMatrix_mul_map_frameMatrixInv : HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((frP S b).map (incA D))
    ((frPinv S b).map (incA D)) = 1 := by
  rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem reW_reWinv (x : WO S T) : reW S T b (reWinv S T b x) = x :=
  mul_mul_cancel x _ _ (map_frameMatrix_mul_map_frameMatrixInv S b)

theorem reWinv_reW (x : WO (reS S b) T) : reWinv S T b (reW S T b x) = x :=
  mul_mul_cancel x _ _ (frPinv_frP_A S b)

theorem reW_add (x y : WO (reS S b) T) : reW S T b (x + y) = reW S T b x + reW S T b y :=
  Matrix.add_mul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) y _

theorem reW_zero : reW S T b 0 = 0 :=
  Matrix.zero_mul (α := AE D) (l := Fin T.rank) ((frPinv S b).map (incA D))

theorem reWinv_add (x y : WO S T) : reWinv S T b (x + y) = reWinv S T b x + reWinv S T b y :=
  Matrix.add_mul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) y _

theorem reWinv_continuous : Continuous (reWinv S T b) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  unfold reWinv
  exact continuous_id.matrix_mul continuous_const

def reWAdd : WO (reS S b) T →+ WO S T where
  toFun := reW S T b
  map_zero' := reW_zero S T b
  map_add' := reW_add S T b

def reWHomeo : WO (reS S b) T ≃ₜ WO S T where
  toFun := reW S T b
  invFun := reWinv S T b
  left_inv := reWinv_reW S T b
  right_inv := reW_reWinv S T b
  continuous_toFun := reW_continuous S T b
  continuous_invFun := reWinv_continuous S T b

def reFEquiv : (WO S T → ℂ) ≃ₗ[ℂ] (WO (reS S b) T → ℂ) :=
  { reF S T b with
    invFun := fun f x => f (reWinv S T b x)
    left_inv := fun f => funext fun x => by
      show f (reW S T b (reWinv S T b x)) = f x
      rw [reW_reWinv]
    right_inv := fun f => funext fun x => by
      show f (reWinv S T b (reW S T b x)) = f x
      rw [reWinv_reW] }

theorem hO_eq_trace (V : HSp D) (x y : WO V T) :
    hO V T x y = Matrix.trace (((V.gram⁻¹).map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D)) * x) := by
  simp only [hO, Matrix.trace, Matrix.mul_apply, Matrix.diag, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun d _ => Finset.sum_comm

theorem inv_gram_re : ((reS S b).gram⁻¹ : Matrix (Fin S.rank) (Fin S.rank) D.host.E) =
    frPinv S b * S.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frPinv S b) := by
  have h := (isoPair_re S b).2.2.1
  have e1 : (frP S b)⁻¹ = frPinv S b := Matrix.inv_eq_left_inv (frPinv_mul_frP S b)
  have e2 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frP S b))⁻¹ =
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frPinv S b) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Formalism.UG.cT_mul, frameMatrix_mul_frameMatrixInv, Formalism.UG.cT_one]
  have h' : ((reS S b).gram : Matrix (Fin S.rank) (Fin S.rank) D.host.E) =
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frP S b) * S.gram * frP S b := h.symm
  rw [h', Matrix.mul_inv_rev, Matrix.mul_inv_rev, e1, e2, Matrix.mul_assoc]

theorem trace_inverseGram_conj_smul_eq {R : Type*} [CommRing R] (c : R →+* R) {m n : ℕ} (Gi Gi' P : Matrix (Fin n) (Fin n) R)
    (GT : Matrix (Fin m) (Fin m) R)
    (x y : Matrix (Fin m) (Fin n) R) (h : P * Gi * (P.map c)ᵀ = Gi') :
    Matrix.trace (Gi * ((y * P).map c)ᵀ * GT * (x * P)) = Matrix.trace (Gi' * (y.map c)ᵀ * GT * x) := by
  rw [Matrix.map_mul, Matrix.transpose_mul, ← h]
  rw [show Gi * ((P.map c)ᵀ * (y.map c)ᵀ) * GT * (x * P) =
    (Gi * (P.map c)ᵀ * ((y.map c)ᵀ * GT * x)) * P by simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem gram_key : HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D))
    (HMul.hMul (α := Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((frPinv S b).map (incA D)) ((S.gram⁻¹).map (incA D)))
      ((((frPinv S b).map (incA D)).map (cA D))ᵀ) =
    (((reS S b).gram⁻¹ : Matrix (Fin S.rank) (Fin S.rank) D.host.E)).map (incA D) := by
  rw [inv_gram_re]
  have e : (((frPinv S b).map (incA D)).map (cA D))ᵀ =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frPinv S b)).map (incA D) := by
    ext i j; rfl
  rw [e, Matrix.map_mul, Matrix.map_mul]

theorem hO_reW (x y : WO (reS S b) T) : hO S T (reW S T b x) (reW S T b y) = hO (reS S b) T x y := by
  rw [hO_eq_trace, hO_eq_trace]
  exact trace_inverseGram_conj_smul_eq (cA D) _ _ _ _ x y (gram_key S b)

theorem symplOH_reW (x y : WO (reS S b) T) :
    symplOH S T (reW S T b x) (reW S T b y) = symplOH (reS S b) T x y := by
  simp only [symplOH, symplO, hO_reW]

theorem heisO_reF (ψ : AddChar (AF D.host.F) ℂ) (w : WO (reS S b) T) (f : WO S T → ℂ) :
    heisO ψ (reS S b) T w (reF S T b f) = reF S T b (heisO ψ S T (reW S T b w) f) := by
  funext x
  simp only [heisO, reF_apply, reW_add, symplOH_reW]

theorem reW_ratW (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    reW S T b (ratW T (reS S b) γ) = ratW T S (γ * frPinv S b) :=
  (Matrix.map_mul (f := incA D) (L := γ) (M := frPinv S b)).symm

theorem reWinv_ratW (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    reWinv S T b (ratW T S γ) = ratW T (reS S b) (γ * frP S b) :=
  (Matrix.map_mul (f := incA D) (L := γ) (M := frP S b)).symm

theorem mem_ratL_reW (x : WO (reS S b) T) : reW S T b x ∈ ratL T S ↔ x ∈ ratL T (reS S b) := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ * frP S b, ?_⟩
    have h1 : reWinv S T b (ratW T S γ) = x := by
      rw [← reWinv_reW S T b x]; exact congrArg (reWinv S T b) hγ
    rw [reWinv_ratW] at h1
    exact h1
  · rintro ⟨γ, hγ⟩
    refine ⟨HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) D.host.E) γ (frPinv S b), ?_⟩
    have h1 : reW S T b (ratW T (reS S b) γ) = reW S T b x := congrArg (reW S T b) hγ
    exact (reW_ratW S T b γ).symm.trans h1

theorem block_frame_conjugation_identity {R : Type*} [Ring R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R)
    (M P Pi : Matrix (Fin n) (Fin n) R) (h : Pi * P = 1) : A * x * M * Pi = A * (x * Pi) * (P * M * Pi) := by
  rw [show A * (x * Pi) * (P * M * Pi) = A * x * (Pi * P) * M * Pi by simp only [Matrix.mul_assoc], h,
    Matrix.mul_one]

theorem reW_actO (h : GA D (reS S b)) (g : GA D T) (x : WO (reS S b) T) :
    reW S T b (actO (reS S b) T h g x) = actO S T (reGrp S b h) g (reW S T b x) := by
  unfold actO reW
  rw [← map_inv, mt_reGrp]
  exact block_frame_conjugation_identity _ _ _ _ _ (frPinv_frP_A S b)

theorem map_mul_one {R : Type*} [Semiring R] (f : D.host.E →+* R) {n : ℕ} (A B : Matrix (Fin n) (Fin n) D.host.E)
    (h : A * B = 1) : A.map f * B.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem conj_eq_one_iff {R : Type*} [Ring R] {n : ℕ} (X P Pi : Matrix (Fin n) (Fin n) R) (h1 : P * Pi = 1)
    (h2 : Pi * P = 1) : P * X * Pi = 1 ↔ X = 1 := by
  constructor
  · intro h
    calc X = Pi * (P * X * Pi) * P := by simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]; rw [Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = 1 := by rw [h, Matrix.mul_one, h2]
  · rintro rfl
    rw [Matrix.mul_one, h1]

theorem reGrp_mem_GinfC (h : GA D (reS S b)) : reGrp S b h ∈ GinfC S ↔ h ∈ GinfC (reS S b) := by
  have e := GlobalTheory.VolTransport.conjA_finMat (isoPair_re S b) h
  simp only [GinfC, MonoidHom.mem_ker, Units.ext_iff, finHom_eq, Units.val_one]
  refine Iff.trans (Eq.to_iff (congrArg (· = (1 : Matrix (Fin S.rank) (Fin S.rank) _)) e)) ?_
  exact conj_eq_one_iff _ _ _ (map_mul_one _ _ _ (frameMatrix_mul_frameMatrixInv S b)) (map_mul_one _ _ _ (frPinv_mul_frP S b))

theorem reGrp_mem_GQ (h : GA D (reS S b)) (hh : h ∈ GQ (reS S b)) : reGrp S b h ∈ GQ S :=
  GlobalTheory.VolTransport.conjA_rat (isoPair_re S b) h hh

set_option synthInstance.maxHeartbeats 200000 in
theorem map_mul_eq_zero_iff {R : Type*} [Ring R] {m n : ℕ} (φ : AE D →+* R) (x : Matrix (Fin m) (Fin n) (AE D))
    (P Pi : Matrix (Fin n) (Fin n) D.host.E) (h : Pi * P = 1) :
    (x * Pi.map (incA D)).map φ = 0 ↔ x.map φ = 0 := by
  rw [Matrix.map_mul]
  constructor
  · intro hx
    have hP : (Pi.map (incA D)).map φ * (P.map (incA D)).map φ = 1 := by
      rw [Matrix.map_map, Matrix.map_map]
      exact map_mul_one (φ.comp (incA D)) Pi P h
    have e : x.map φ * (Pi.map (incA D)).map φ * (P.map (incA D)).map φ = x.map φ := by
      rw [Matrix.mul_assoc, hP, Matrix.mul_one]
    rw [← e, hx, Matrix.zero_mul]
  · intro hx; rw [hx, Matrix.zero_mul]

theorem reW_map_eq_zero {R : Type*} [Ring R] (φ : AE D →+* R) (x : WO (reS S b) T) :
    (reW S T b x).map φ = 0 ↔ x.map φ = 0 :=
  map_mul_eq_zero_iff φ x (frP S b) (frPinv S b) (frPinv_mul_frP S b)

end GlobalTheory.AdSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistDatumValueEqProdLocalResidueValuesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistDatumValue_eq_prod_localResidueValues : ∀ (D : D7) (a b r : ℕ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)),
      omegaQ Q r ξ 1 y = ∏ PP ∈ Q, qLoc r PP (ξ PP) (y PP) := by
  first | exact @GlobalTheory.StepVec.omegaQ_one_eq_prod_qLoc | exact GlobalTheory.StepVec.omegaQ_one_eq_prod_qLoc | (intros; apply GlobalTheory.StepVec.omegaQ_one_eq_prod_qLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistPlaceDatumParabolicMoveStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaceDatum_parabolic_move : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (n : ℤ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Q, G PP ∈ blockTri (blk2 r) ∧ H PP ∈ blockTri (blk2 r)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaQ Q r ξ n (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Q, (ξ PP (Matrix.GeneralLinearGroup.det (G PP)) * (ξ PP (dBlk (blk2 r) 1 (G PP)))⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (H PP)))⁻¹ * ξ PP (dBlk (blk2 r) 1 (H PP)))) ^ n : ℂˣ) : ℂ) * omegaQ Q r ξ n y := by
  first | exact @GlobalTheory.ParabolicDatum.omegaQ_parabolic | exact GlobalTheory.ParabolicDatum.omegaQ_parabolic | (intros; apply GlobalTheory.ParabolicDatum.omegaQ_parabolic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlaceDatumBlockTriangularMoveStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaceDatum_blockTriangular_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, G PP ∈ blockTri (blkOf r t) ∧ H PP ∈ blockTri (blkOf r t) ∧ upperLeftBlock ha (G PP) = upperLeftBlock hb (H PP)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G PP))) * (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (H PP)))⁻¹ * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹)) : ℂˣ) : ℂ) * omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) y := by
  first | exact @GlobalTheory.StepLaw.omegaG_blockTri_move | exact GlobalTheory.StepLaw.omegaG_blockTri_move | (intros; apply GlobalTheory.StepLaw.omegaG_blockTri_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryBorelPreservesMixedModelLatticeLowerBlockStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryBorel_preserves_mixedModelLattice_lowerBlock : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (g : GU σ n) (h : GU σ n'), IsBorelU g → IsBorelU h → (∀ a : Matrix (Fin n') (Fin n) L, a ∈ mixLat L n' n → (h.1.1 * a * g.1.1 : Matrix (Fin n') (Fin n) L) ∈ mixLat L n' n) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ∃ a ∈ mixLat L n' n, (∀ (r : Fin n') (c : Fin n), c.1 < n - n / 2 → a r c = 0) ∧ (h.1.1 * embLow n' n z * g.1.1 : Matrix (Fin n') (Fin n) L) = a + embLow n' n (lowBlock h.1.1 * z * lowBlock g.1.1) := by
  first | exact @GlobalTheory.SphTheta.borel_mixLat_lowBlock | exact GlobalTheory.SphTheta.borel_mixLat_lowBlock | (intros; apply GlobalTheory.SphTheta.borel_mixLat_lowBlock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpperTriangularUnitaryLowerHalfBlockTriangularStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperTriangularUnitary_lowerHalfBlock_triangular : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (hn : n ≤ n'), (∀ g : GU σ n, IsBorelU g → ∃ U : GL (Fin (n / 2)) L, U.1 = lowBlock g.1.1 ∧ U.1.BlockTriangular id ∧ ∀ r, ordL (U.1 r r) = -ordL (g.1.1 (lo n r.rev) (lo n r.rev))) ∧ ∀ h : GU σ n', IsBorelU h → ∃ V : GL (Fin (n / 2)) L, V.1.BlockTriangular id ∧ (∀ r : Fin (n / 2), ordL (V.1 r.rev r.rev) = ordL (h.1.1 (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩) (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩))) ∧ ∀ t : Matrix (Fin (n / 2)) (Fin (n / 2)) L, lowBlock (h⁻¹).1.1 * (Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0) = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then (V.1 * t) ⟨r.1, e⟩ c else 0 := by
  first | exact @GlobalTheory.SphTheta.lowBlocks_borel | exact GlobalTheory.SphTheta.lowBlocks_borel | (intros; apply GlobalTheory.SphTheta.lowBlocks_borel <;> assumption)
end

