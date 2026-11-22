import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0992
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientTraceVanishes
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

open GlobalTheory.HCChar GlobalTheory.Orb GlobalTheory.FlagLeviGroup

namespace GlobalTheory.IndTraceZero

variable {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : GlobalTheory.RealInd.Flag n a}

theorem IsSplit.commute (hW : IsIsoFlag ε j W) {x : Fin a → ℝ} {t g : UJ ε} (ht : IsSplit ε W x t)
    (hg : g ∈ flagM ε W) : g * t = t * g := by
  have hgi : g⁻¹ ∈ flagM ε W := (leviSub ε W).inv_mem hg
  have hgg : uMat g * uMat g⁻¹ = 1 := by
    rw [← show uMat (g * g⁻¹) = uMat g * uMat g⁻¹ from rfl, mul_inv_cancel]; rfl
  have hJ : Jm ε * uMat g⁻¹ = (uMat g)ᴴ * Jm ε := by
    have := conjTranspose_inv_mul_Jm (ε := ε) g⁻¹
    rw [inv_inv] at this
    exact this.symm
  have hm : uMat (g * t * g⁻¹) = uMat g * uMat t * uMat g⁻¹ := rfl
  have h' : IsSplit ε W x (g * t * g⁻¹) := by
    refine ⟨(leviSub ε W).mul_mem ((leviSub ε W).mul_mem hg ht.1) hgi, fun i y hy => ?_, fun y hy => ?_⟩
    · have hy' : uMat g⁻¹ *ᵥ y ∈ W i.succ := (hgi _ y hy).1
      have h1 := (hg _ _ (ht.2.1 i _ hy')).1
      have e : uMat g *ᵥ (uMat t *ᵥ (uMat g⁻¹ *ᵥ y) - (Real.exp (x i) : ℂ) • (uMat g⁻¹ *ᵥ y)) =
          uMat (g * t * g⁻¹) *ᵥ y - (Real.exp (x i) : ℂ) • y := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          hgg, Matrix.one_mulVec, hm]
      rwa [e] at h1
    · have hy' : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat g⁻¹ *ᵥ y)) = 0 := fun z hz => by
        rw [Matrix.mulVec_mulVec, hJ, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
        exact hy _ (hg _ z hz).1
      have h1 := (hg _ _ (ht.2.2 _ hy')).1
      have e : uMat g *ᵥ (uMat t *ᵥ (uMat g⁻¹ *ᵥ y) - uMat g⁻¹ *ᵥ y) = uMat (g * t * g⁻¹) *ᵥ y - y := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgg,
          Matrix.one_mulVec, hm]
      rwa [e] at h1
  have e := (existsUnique_isSplit hW x).unique h' ht
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [e]

theorem not_isSplit_subset_compact (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) (ha : a ≠ 0) {K : Set (UJ ε)}
    (hK : IsCompact K) (h : ∀ r : ℝ, ∃ t ∈ K, IsSplit ε W (fun _ => r) t) : False := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  let i₀ : Fin (a' + 1) := 0
  have hr : Module.finrank ℂ (W i₀.succ) = j i₀ := by
    rw [hW.2.2.1 i₀, show i₀.castSucc = 0 from rfl, hW.1, finrank_bot, zero_add]
  have hne : W i₀.succ ≠ ⊥ := fun e => by
    have := hj i₀
    rw [e, finrank_bot] at hr
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hc : Continuous fun g : UJ ε => uMat g *ᵥ y :=
    (continuous_ujMat (ε := ε)).matrix_mulVec continuous_const
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  obtain ⟨t, htK, ht⟩ := h (C / ‖y‖)
  have h1 := ht.2.1 i₀ y hy
  rw [show i₀.castSucc = 0 from rfl, hW.1, Submodule.mem_bot, sub_eq_zero] at h1
  have h2 := hC t htK
  rw [h1, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h2
  have h3 := Real.add_one_le_exp (C / ‖y‖)
  have h4 : (C / ‖y‖ + 1) * ‖y‖ ≤ C := (mul_le_mul_of_nonneg_right h3 hyn.le).trans h2
  rw [add_mul, div_mul_cancel₀ _ hyn.ne', one_mul] at h4
  linarith

theorem not_conj_mem_flagM (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) (ha : a ≠ 0) {s : UJ ε}
    (hK : IsCompact (cent s : Set (UJ ε))) (x : UJ ε) : x * s * x⁻¹ ∉ flagM ε W := by
  intro hx
  refine not_isSplit_subset_compact hW hj ha (hK.image (f := fun g => x * g * x⁻¹)
    ((continuous_const.mul continuous_id).mul continuous_const)) fun r => ?_
  obtain ⟨t, ht, -⟩ := exists_isSplit hW (fun _ => r)
  have hc := IsSplit.commute hW ht hx
  refine ⟨t, ⟨x⁻¹ * t * x, mem_cent.2 ?_, by group⟩, ht⟩
  calc x⁻¹ * t * x * s = x⁻¹ * (t * (x * s * x⁻¹)) * x := by group
    _ = x⁻¹ * ((x * s * x⁻¹) * t) * x := by rw [hc]
    _ = s * (x⁻¹ * t * x) := by group

end GlobalTheory.IndTraceZero

namespace GlobalTheory.IndTraceZero

open GlobalTheory.HCChar GlobalTheory.Published

theorem hasTrace_indModule_eq_zero : GlobalTheory.Published.HarishChandraCharacters → ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : UJ ε →* (X →L[ℂ] X)) (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ δ f → ∀ I : IndModule ε, I.a ≠ 0 → HasTrace (repOp I.rep μ f) 0 := by
  intro hHC n ε μ _ X _ _ _ δ f hf I ha
  obtain ⟨Θ, hΘ, hvan⟩ := hHC.2.2.2.indModule μ I ha
  have htr := hΘ.1.2.2 f hf.mem
  convert htr using 1
  symm
  refine hHC.2.2.1.integral_mul_eq_zero μ (continuous_of_mem_ccSmooth isInducing_matCoord.continuous hf.mem)
    hf.mem.1 hΘ.1.1 (fun s x hs => (hΘ.2 s hs).2 x) fun s hs => ?_
  by_cases hK : IsCompact (cent s : Set (UJ ε))
  · exact Or.inl (hvan s hs fun x => not_conj_mem_flagM I.flag I.pos ha hK x)
  · exact Or.inr fun ds _ _ => hf.orb_noncompact s hs hK ds

end GlobalTheory.IndTraceZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReAddIm
section
noncomputable section

open Formalism.BasicNotions.TH Matrix
open scoped InnerProductSpace

namespace GlobalTheory.RealPartAdjointAction

variable {r s : ℕ}

theorem J_ct : (Jm r s)ᴴ = Jm r s := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem J_sq : Jm r s * Jm r s = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem J_J (X : Mat r s) : Jm r s * (Jm r s * X) = X := by
  rw [← Matrix.mul_assoc, J_sq, Matrix.one_mul]

def reP (Z : Mat r s) : Mat r s := (1 / 2 : ℂ) • (Z - adjZ Z)

def imaginary (Z : Mat r s) : Mat r s := (-Complex.I / 2 : ℂ) • (Z + adjZ Z)

theorem adj_ct_J (Z : Mat r s) : (adjZ Z)ᴴ * Jm r s = Jm r s * Z := by
  simp only [adjZ, Matrix.conjTranspose_mul, J_ct, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, J_sq,
    Matrix.mul_one]

theorem J_adj (Z : Mat r s) : Jm r s * adjZ Z = Zᴴ * Jm r s := by
  simp only [adjZ, Matrix.mul_assoc, J_J]

theorem adj_adj (Z : Mat r s) : adjZ (adjZ Z) = Z := by
  have h : adjZ (adjZ Z) = Jm r s * ((adjZ Z)ᴴ * Jm r s) := Matrix.mul_assoc _ _ _
  rw [h, adj_ct_J, J_J]

theorem realPart_mem_unitaryLieAlgebra (Z : Mat r s) : reP Z ∈ upq r s := by
  have h : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [upq, reP, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, adj_ct_J, J_adj, h]
  module

theorem imaginaryPart_mem_unitaryLieAlgebra (Z : Mat r s) : imaginary Z ∈ upq r s := by
  have h : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by simp
  simp only [upq, imaginary, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, adj_ct_J, J_adj, h]
  module

theorem re_add_im (Z : Mat r s) : reP Z + Complex.I • imaginary Z = Z := by
  have h : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I, neg_neg]
  rw [reP, imaginary, smul_smul, h]
  module

theorem realPart_adjoint (Z : Mat r s) : reP (adjZ Z) = (-1 : ℝ) • reP Z := by
  rw [reP, reP, adj_adj, neg_one_smul, ← smul_neg, neg_sub]

theorem imaginaryPart_adjoint (Z : Mat r s) : imaginary (adjZ Z) = imaginary Z := by
  rw [imaginary, imaginary, adj_adj, add_comm]

section Main

variable {W U I : Type} [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  (a : Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Mat r s → Module.End ℂ U) (j : I → W →ₗ[ℂ] U)

def cx (Z : Mat r s) : Module.End ℂ U := b (reP Z) + Complex.I • b (imaginary Z)

def Sp : Submodule ℂ U := Submodule.span ℂ {y : U | ∃ (i : I) (P : W), y = j i P}

def jS (i : I) : W →ₗ[ℂ] Sp j := (j i).codRestrict (Sp j) fun P => Submodule.subset_span ⟨i, P, rfl⟩

theorem gen (K : Submodule ℂ (Sp j)) (h : ∀ i P, jS j i P ∈ K) (y : Sp j) : y ∈ K := by
  obtain ⟨y, hy⟩ := y
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, P, rfl⟩ := hx
    exact h i P
  | zero => exact K.zero_mem
  | add x y hx hy ihx ihy => exact K.add_mem ihx ihy
  | smul c x hx ih => exact K.smul_mem c ih

theorem ext_gen {N : Type} [AddCommGroup N] [Module ℂ N] (f g : Sp j →ₗ[ℂ] N)
    (h : ∀ i P, f (jS j i P) = g (jS j i P)) : f = g :=
  LinearMap.ext fun y => gen j (LinearMap.eqLocus f g) h y

def Eqv : Prop := ∀ i, ∀ Z ∈ upq r s, ∀ P, j i (a Z P) = b Z (j i P)

variable {a b j}

theorem cx_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : cx b Z (j i P) = j i (a Z P) := by
  conv_rhs => rw [← re_add_im Z]
  simp only [cx, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h i _ (realPart_mem_unitaryLieAlgebra Z), h i _ (imaginaryPart_mem_unitaryLieAlgebra Z)]

theorem stab (f : Module.End ℂ U) (Z : Mat r s) (hf : ∀ i P, f (j i P) = j i (a Z P)) :
    ∀ y ∈ Sp j, f y ∈ Sp j := by
  have : Sp j ≤ (Sp j).comap f := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, P, rfl⟩
    show f (j i P) ∈ Sp j
    rw [hf]
    exact Submodule.subset_span ⟨i, _, rfl⟩
  exact fun y hy => this hy

def op (h : Eqv a b j) (Z : Mat r s) : Module.End ℂ (Sp j) := (cx b Z).restrict (stab _ Z (cx_gen h Z))

theorem op_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : op h Z (jS j i P) = jS j i (a Z P) :=
  Subtype.ext (cx_gen h Z i P)

def act (h : Eqv a b j) : Mat r s →ₗ[ℂ] Module.End ℂ (Sp j) where
  toFun := op h
  map_add' X Y := ext_gen j _ _ fun i P => by
    simp only [LinearMap.add_apply, op_gen, map_add]
  map_smul' c X := ext_gen j _ _ fun i P => by
    simp only [LinearMap.smul_apply, op_gen, map_smul, RingHom.id_apply]

theorem act_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : act h Z (jS j i P) = jS j i (a Z P) :=
  op_gen h Z i P

theorem act_coe (h : Eqv a b j) (Z : Mat r s) (y : Sp j) : (act h Z y : U) = cx b Z y := rfl

def finPart {V : Type} [AddCommGroup V] [Module ℂ V] (c : Mat r s →ₗ[ℂ] Module.End ℂ V) : Submodule ℂ V where
  carrier := {v | ∃ F : Submodule ℂ V, FiniteDimensional ℂ F ∧ v ∈ F ∧ KStable c F}
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, fun X _ w hw => by
    rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro x y ⟨F, hF, hx, kF⟩ ⟨G, hG, hy, kG⟩
    refine ⟨F ⊔ G, inferInstance, Submodule.add_mem_sup hx hy, fun X hX w hw => ?_⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    exact Submodule.add_mem_sup (kF X hX u hu) (kG X hX v hv)
  smul_mem' := by
    rintro t x ⟨F, hF, hx, kF⟩
    exact ⟨F, hF, F.smul_mem t hx, kF⟩

def spanMod (ha : GlobalTheory.ArchRec.IsGK a) (h : Eqv a b j) : GKMod r s where
  V := Sp j
  act := act h
  lie X Y := ext_gen j _ _ fun i P => by
    simp only [act_gen, ha.1 X Y, LinearMap.sub_apply, Module.End.mul_apply, map_sub (jS j i)]
  kfin := gen j (finPart (act h)) fun i P => by
    obtain ⟨F, hF, hP, kF⟩ := ha.2.1 P
    refine ⟨F.map (jS j i), inferInstance, Submodule.mem_map_of_mem hP, ?_⟩
    rintro X hX _ ⟨w, hw, rfl⟩
    rw [act_gen]
    exact Submodule.mem_map_of_mem (kF X hX w hw)
  wts := gen j _ fun i P => by
    have hle : (⨆ μ : Ix r s → ℚ, wtSub a μ) ≤ (⨆ μ : Ix r s → ℚ, wtSub (act h) μ).comap (jS j i) := by
      refine iSup_le fun μ w hw => Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hw ⊢
      intro c
      rw [act_gen, ← map_smul, ← map_sub, hw c, map_zero]
    exact hle (ha.2.2 P)

theorem cx_adj (hb : GlobalTheory.ArchRec.IsUAct b) (Z : Mat r s) (x y : U) :
    ⟪cx b Z x, y⟫_ℂ = ⟪x, cx b (adjZ Z) y⟫_ℂ := by
  simp only [cx, realPart_adjoint, imaginaryPart_adjoint, hb.smul _ _ (realPart_mem_unitaryLieAlgebra Z), LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hb.skew _ (realPart_mem_unitaryLieAlgebra Z),
    hb.skew _ (imaginaryPart_mem_unitaryLieAlgebra Z), Complex.conj_I]
  push_cast
  ring

def spanUMod (ha : GlobalTheory.ArchRec.IsGK a) (hb : GlobalTheory.ArchRec.IsUAct b) (h : Eqv a b j) : UGKMod r s where
  M := spanMod ha h
  ip := innerₛₗ ℂ (E := Sp j)
  herm x y := inner_conj_symm (𝕜 := ℂ) (E := Sp j) y x
  pos x hx := (re_inner_self_pos (𝕜 := ℂ) (E := Sp j)).2 hx
  adj Z x y := cx_adj hb Z (x : Sp j).1 (y : Sp j).1

theorem act_real (h : Eqv a b j) (Z : Mat r s) (hZ : Z ∈ upq r s) (y : Sp j) : (act h Z y : U) = b Z y := by
  have := ext_gen j ((Sp j).subtype ∘ₗ act h Z) (b Z ∘ₗ (Sp j).subtype) fun i P => by
    rw [LinearMap.comp_apply, act_gen]
    exact h i Z hZ P
  exact LinearMap.congr_fun this y

end Main

theorem main : ∀ (r s : ℕ) (W U I : Type) [inst : AddCommGroup W] [inst_1 : Module ℂ W] [inst_2 : NormedAddCommGroup U] [inst_3 : InnerProductSpace ℂ U] (a : Formalism.BasicNotions.TH.Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ U) (j : I → W →ₗ[ℂ] U), GlobalTheory.ArchRec.IsGK a → GlobalTheory.ArchRec.IsUAct b → (∀ (i : I), ∀ Z ∈ Formalism.BasicNotions.TH.upq r s, ∀ (P : W), (j i : W → U) (((a : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ W) Z : W → W) P) = (b Z : U → U) ((j i : W → U) P)) → ∃ (MM : Formalism.BasicNotions.TH.UGKMod r s) (inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) →ₗ[ℂ] U), Function.Injective (⇑inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) ∧ LinearMap.range inc = Submodule.span ℂ {y : U | ∃ (i : I) (P : W), y = (j i : W → U) P} ∧ ∀ Z ∈ Formalism.BasicNotions.TH.upq r s, ∀ (y : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM)), (inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) (((Formalism.BasicNotions.TH.GKMod.act (Formalism.BasicNotions.TH.UGKMod.M MM) : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ (Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM))) Z : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM)) y) = (b Z : U → U) ((inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) y) := by
  intro r s W U I _ _ _ _ a b j ha hb h
  exact ⟨spanUMod ha hb h, (Sp j).subtype, (Sp j).injective_subtype, (Sp j).range_subtype,
    fun Z hZ y => act_real h Z hZ y⟩

end GlobalTheory.RealPartAdjointAction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerContractionValuesKFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLineKFin

private theorem eq_of_inner_eq_on_dense {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E : Submodule ℂ H} (hE : Dense (E : Set H)) {v w : H}
    (h : ∀ y : E, ⟪v, (y : H)⟫_ℂ = ⟪w, (y : H)⟫_ℂ) : v = w := by
  have hclosed : IsClosed {x : H | ⟪v - w, x⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : (E : Set H) ⊆ {x : H | ⟪v - w, x⟫_ℂ = 0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, inner_sub_left, h ⟨x, hx⟩, sub_self]
  have hall := closure_minimal hsub hclosed
  rw [hE.closure_eq] at hall
  have hz : ⟪v - w, v - w⟫_ℂ = 0 := hall (Set.mem_univ _)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem exists_riesz {H P : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup P] [Module ℂ P] {E : Submodule ℂ H} (hE : Dense (E : Set H)) (F : P →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hF : ∀ φ, ∃ c : ℝ, ∀ y : E, ‖F φ y‖ ≤ c * ‖(y : H)‖) :
    ∃ b : P →ₛₗ[starRingEnd ℂ] H, ∀ φ (y : E), F φ y = ⟪b φ, (y : H)⟫_ℂ := by
  have hrep : ∀ φ, ∃ v : H, ∀ y : E, F φ y = ⟪v, (y : H)⟫_ℂ := by
    intro φ
    obtain ⟨c, hc⟩ := hF φ
    have hden : DenseRange (E.subtype : E →ₗ[ℂ] H) := by
      simpa using hE.denseRange_val
    let g : H →L[ℂ] ℂ := (F φ).extendOfNorm E.subtype
    refine ⟨(InnerProductSpace.toDual ℂ H).symm g, fun y => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    have := LinearMap.extendOfNorm_eq (f := F φ) hden ⟨c, fun y => by simpa using hc y⟩ y
    simpa [g] using this.symm
  choose v hv using hrep
  refine ⟨{ toFun := v, map_add' := ?_, map_smul' := ?_ }, hv⟩
  · intro φ ψ
    refine eq_of_inner_eq_on_dense hE fun y => ?_
    rw [← hv, inner_add_left, ← hv, ← hv, map_add, LinearMap.add_apply]
  · intro c φ
    refine eq_of_inner_eq_on_dense hE fun y => ?_
    rw [← hv, inner_smul_left, ← hv, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp

theorem finite_map {H P : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup P] [Module ℂ P]
    (b : P →ₛₗ[starRingEnd ℂ] H) (T : Submodule ℂ P) [FiniteDimensional ℂ T] : FiniteDimensional ℂ (T.map b) := by
  have hT : (T : Submodule ℂ P).FG := Module.Finite.iff_fg.mp inferInstance
  exact Module.Finite.iff_fg.mpr (hT.map b)

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sm_stable (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.MainNotions.S.UJset (M.ε τ)) {y : M.H τ} (hy : y ∈ M.sm τ) : M.σ τ g y ∈ M.sm τ := Submodule.subset_span (GlobalTheory.ConjExt.smooth_translate M τ ⟨y, hy⟩ hg)

theorem dense_sm (M : DSModel V S) (τ : D.what₂.Tau) : Dense (M.sm τ : Set (M.H τ)) := GlobalTheory.LowTypeDetermined.dense_of_irred (M.ds τ).2.2.2.1 (fun _ hg _ hy => sm_stable M τ hg hy) (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)

theorem kset_star {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    star k ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact Matrix.mem_unitaryGroup_iff'.mp hu), ?_⟩
  have hJ : star (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
    rw [Matrix.star_eq_conjTranspose]; exact Formalism.REAL.Jm_conjTranspose ε
  calc star k * Formalism.REAL.Jm ε = star (Formalism.REAL.Jm ε * k) := by rw [star_mul, hJ]
    _ = star (k * Formalism.REAL.Jm ε) := by rw [hc]
    _ = Formalism.REAL.Jm ε * star k := by rw [star_mul, hJ]

private theorem mem_UJset_of_mem_Kset_twisted_operators {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) : k ∈ Formalism.MainNotions.S.UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have hkk : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  simp only [Formalism.MainNotions.S.UJset, Set.mem_ofPred_eq, Formalism.REAL.inUJ]
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hkk, Matrix.one_mul]

private theorem subst_subst_eq_of_subst_eq_X {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (y : H) : σ k (σ (star k) y) = y := by
  have hks1 : k * star k = 1 := Matrix.mem_unitaryGroup_iff.mp hk.1
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 k (mem_UJset_of_mem_Kset_twisted_operators hk) (star k) (mem_UJset_of_mem_Kset_twisted_operators (kset_star hk)),
    hks1, hσ.1.1]
  rfl

private theorem inner_urep_apply_eq_inner_star_of_mem_Kset {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (x y : H) :
    ⟪σ k x, y⟫_ℂ = ⟪x, σ (star k) y⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ k).toLinearMap, hσ.2.1 k (mem_UJset_of_mem_Kset_twisted_operators hk)⟩
  conv_lhs => rw [← subst_subst_eq_of_subst_eq_X hσ hk y]
  exact L.inner_map_map x (σ (star k) y)

theorem kfin : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (aS aT : ℚ) (A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), SemiW M M' τ aS aT A → (∀ φ y, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) (A φ y)) ∧ ∀ φ u, ∃ b : M'.H τ, Formalism.MainNotions.S.IsKFin (M'.ε τ) (M'.σ τ) b ∧ ∀ y : M'.sm τ, ⟪u, A φ y⟫_ℂ = ⟪b, (y : M'.H τ)⟫_ℂ := by
  intro D V W S S' M M' τ aS aT A hA
  have : CompleteSpace (M'.H τ) := (M'.ds τ).1
  refine ⟨fun φ y => ?_, fun φ u => ?_⟩
  · refine ⟨(MvPolynomial.restrictTotalDegree _ ℂ φ.totalDegree).map (A.flip y), ?_, ⟨φ, ?_, rfl⟩, ?_⟩
    · exact Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp inferInstance).map _)
    · exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl
    · intro g hg v hv
      obtain ⟨ψ, hψ, rfl⟩ := hv
      obtain ⟨ψ', hdeg, heq⟩ := hA.eqK g hg ψ
      refine ⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
        (hdeg.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hψ)), ?_⟩
      simp only [LinearMap.flip_apply, heq y]
  · let F : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] ℂ := A.compr₂ (innerSL ℂ u).toLinearMap
    have hFapp : ∀ ψ y, F ψ y = ⟪u, A ψ y⟫_ℂ := fun ψ y => by simp [F]
    obtain ⟨b, hb⟩ := exists_riesz (dense_sm M' τ) F fun ψ => by
      obtain ⟨c, hc⟩ := hA.bdd ψ u
      exact ⟨c, fun y => by rw [hFapp]; exact hc y⟩
    have hσ := (M'.ds τ).2.2.1
    let T : Submodule ℂ (PolF D W.rank V.rank) := MvPolynomial.restrictTotalDegree _ ℂ φ.totalDegree
    refine ⟨b φ, ⟨T.map b, finite_map b T, ⟨φ, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl, rfl⟩, ?_⟩,
      fun y => by rw [← hFapp, hb]⟩
    intro k hk v hv
    obtain ⟨ψ, hψ, rfl⟩ := hv
    obtain ⟨ψ', hdeg, heq⟩ := hA.invK k hk ψ
    have key : M'.σ τ k (b ψ) = b ψ' := by
      refine eq_of_inner_eq_on_dense (dense_sm M' τ) fun y => ?_
      have hmem : M'.σ τ (star k) y ∈ M'.sm τ := sm_stable M' τ (mem_UJset_of_mem_Kset_twisted_operators (kset_star hk)) y.2
      rw [inner_urep_apply_eq_inner_star_of_mem_Kset hσ hk]
      have e1 : F ψ ⟨_, hmem⟩ = ⟪b ψ, M'.σ τ (star k) y⟫_ℂ := hb ψ ⟨_, hmem⟩
      rw [← e1, ← hb ψ' y, hFapp, hFapp, heq ⟨_, hmem⟩ y (subst_subst_eq_of_subst_eq_X hσ hk y).symm]
    rw [key]
    exact ⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      (hdeg.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hψ)), rfl⟩

end GlobalTheory.Chain.RealLineKFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RefinedFlagHalfSumOfRoots
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RhoSum

theorem rho_one_eq {b : ℕ} (n : ℕ) (l : Fin b) :
    rho n (fun _ => 1) l = (n : ℂ) - 2 * (l : ℕ) - 1 := by
  simp [rho, Fin.card_Iio]

theorem sum_range_aff (n P j : ℕ) :
    ∑ m ∈ range j, ((n : ℂ) - 2 * ((P + m : ℕ) : ℂ) - 1) = (j : ℂ) * ((n : ℂ) - 2 * P - j) := by
  induction j with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

theorem filter_lt_eq_Iio {a : ℕ} (i : Fin a) :
    univ.filter (fun l : Fin a => (l : ℕ) < (i.castSucc : ℕ)) = Iio i := by
  ext l
  rw [mem_filter, mem_Iio, Fin.coe_castSucc, Fin.lt_iff_val_lt_val]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

theorem filter_lt_succ {a : ℕ} (i : Fin a) :
    univ.filter (fun l : Fin a => (l : ℕ) < (i.succ : ℕ)) = insert i (Iio i) := by
  ext l
  rw [mem_filter, mem_insert, mem_Iio, Fin.val_succ, Fin.lt_iff_val_lt_val, Fin.ext_iff]
  constructor
  · rintro ⟨-, h⟩; omega
  · intro h; exact ⟨mem_univ _, by omega⟩

theorem card_and_rho_sum : ∀ {a b : ℕ} (n : ℕ) (j : Fin a → ℕ) {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → (∀ i, (p i : ℕ) = ∑ l ∈ univ.filter (fun l : Fin a => (l : ℕ) < (i : ℕ)), j l) → ∀ i, #{l | β l = i} = j i ∧ ∑ l with β l = i, rho n (fun _ => 1) l = (j i : ℂ) * rho n j i := by
  intro a b n j β p hβ hp i
  set P : ℕ := (p i.castSucc : ℕ) with hP
  set Q : ℕ := (p i.succ : ℕ) with hQ
  have hPsum : (P : ℂ) = ∑ l ∈ Iio i, (j l : ℂ) := by
    rw [hP, hp, filter_lt_eq_Iio]; push_cast; rfl
  have hQP : Q = P + j i := by
    rw [hQ, hP, hp, hp, filter_lt_succ, filter_lt_eq_Iio, sum_insert (by simp), add_comm]
  have hQb : Q ≤ b := Nat.lt_succ_iff.mp (p i.succ).isLt
  have hmap : (univ.filter (fun l => β l = i)).map Fin.valEmbedding = Ico P (P + j i) := by
    ext x
    rw [mem_map, mem_Ico]
    constructor
    · rintro ⟨l, hl, rfl⟩
      rw [mem_filter, hβ, Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.coe_castSucc] at hl
      simp only [Fin.valEmbedding_apply]
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, by omega⟩, ?_, rfl⟩
      rw [mem_filter, hβ, Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
      exact ⟨mem_univ _, by simp only; omega, by simp only; omega⟩
  constructor
  · rw [← card_map Fin.valEmbedding, hmap, Nat.card_Ico]; omega
  · have : ∑ l with β l = i, rho n (fun _ => 1) l
        = ∑ x ∈ (univ.filter (fun l => β l = i)).map Fin.valEmbedding, ((n : ℂ) - 2 * (x : ℂ) - 1) := by
      rw [sum_map]; exact sum_congr rfl fun l _ => rho_one_eq n l
    rw [this, hmap, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, sum_range_aff, rho, hPsum]
end GlobalTheory.RhoSum
end

