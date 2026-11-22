import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRangeOfSteps
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FsubMinorMinus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0437
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFrameStabOfParFlag
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResLineLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField E] in

theorem initCols_zero {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : initCols X 0 = col X :=
  Matrix.ext fun i j => congrArg (X i) (Fin.ext (Nat.lt_one_iff.1 j.2))

theorem mem_frameStab_of_parFlag {s : ℕ} {C : Matrix (Fin n) (Fin s) E} {L : Matrix (Fin s) (Fin n) E} (hL : L * C = 1)
    {d : Fin s → ℕ} {g : GAd σ J} (hg : g ∈ GlobalTheory.UAut.parFlag σ J C d) : g ∈ frameStab σ J C ⊤ := by
  obtain ⟨⟨B, -, e⟩, B', -, e'⟩ := hg
  have hL' : adMat F L * adMat F C = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMM : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hBB : B * B' = 1 := by
    calc B * B' = adMat F L * (adMat F C * B) * B' := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
      _ = adMat F L * ((matHom _ σ J g).1 * ((matHom _ σ J g⁻¹).1 * adMat F C)) := by
          simp only [← e, e', Matrix.mul_assoc]
      _ = 1 := by rw [← Matrix.mul_assoc (matHom _ σ J g).1, hMM, Matrix.one_mul, hL']
  exact ⟨⟨B, B', hBB, mul_eq_one_comm.1 hBB⟩, Subgroup.mem_top _, e⟩

omit [NumberField E] in

theorem unipRad_fix {s : ℕ} {C : Matrix (Fin n) (Fin s) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  have : unipRad σ J C ≤ frameStab σ J C ⊥ := (Subgroup.closure_le _).2 fun g hg => ⟨1, one_mem _, by
    have h := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    rw [h, Units.val_one, Matrix.mul_one]⟩
  obtain ⟨B, hB, e⟩ := this hu
  rw [e, Subgroup.mem_bot.1 hB, Units.val_one, Matrix.mul_one]

omit [NumberField E] in

theorem scales_inv {x : Matrix (Fin n) (Fin 1) E} {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ} (e : Scales σ J x p l) :
    Scales σ J x p⁻¹ l⁻¹ := by
  unfold Scales at *
  have := congrArg (fun Z => (l⁻¹).1 • ((matHom _ σ J p⁻¹).1 * Z)) e
  simp only [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
    Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul] at this
  exact this.symm

theorem levi_dec_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ p l, Scales σ J (col X) p l → ∃ u ∈ unipRad σ J (col X), ∃ m ∈ levi σ J X Y {0}, p = u * m ∧ Scales σ J (col X) m l ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) ∧ (absE F E l = 1 → m ∈ leviOne σ J X Y {0}) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW p l hp
  have sub : ∀ A B : Matrix (Fin n) (Fin (r + 1)) E, Formalism.UG.cT (σ : E →+* E) (col A) * J * col B =
      (Formalism.UG.cT (σ : E →+* E) A * J * B).submatrix (fun _ => 0) fun _ => 0 := fun A B => rfl
  have one : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E).submatrix (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) = 1 :=
    Matrix.ext fun i j => by obtain rfl := Subsingleton.elim i j; simp
  have xy : Formalism.UG.cT (σ : E →+* E) (col X) * J * col Y = 1 := by rw [sub, hW.xy, one]
  have yx' : Formalism.UG.cT (σ : E →+* E) (col Y) * J * col X = 1 := by rw [sub, yx h hJ hW, one]
  have sc : ∀ {g : GAd σ J} {l : (AF F ⊗[F] E)ˣ}, Scales σ J (col X) g l →
      (matHom _ σ J g).1 * adMat F (col X) = adMat F (col X) * (l.1 • (1 : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E))) :=
    fun e => by rw [Matrix.mul_smul, Matrix.mul_one]; exact e
  have hpF : p ∈ GlobalTheory.UAut.parFlag σ J (col X) fun _ => 0 :=
    ⟨⟨_, fun _ _ hlt => absurd hlt (lt_irrefl _), sc hp⟩, _, fun _ _ hlt => absurd hlt (lt_irrefl _), sc (scales_inv hp)⟩
  obtain ⟨u, hu, m, hmF, hpm, hr⟩ := (GlobalTheory.LeviFlag.levi_decomposition F E σ h n J hJ 1 (col X) (col Y) (fun _ => 0)
    (by rw [sub, hW.xx]; rfl) (by rw [sub, hW.yy]; rfl) xy).1 p hpF
  rw [GlobalTheory.UAut.unipFlag_const] at hu
  have hm : m ∈ levi σ J X Y {0} := by
    simp only [levi, Subgroup.mem_iInf, Finset.mem_singleton]
    rintro k rfl
    rw [initCols_zero, initCols_zero]
    exact ⟨mem_frameStab_of_parFlag yx' hmF.1, mem_frameStab_of_parFlag xy hmF.2⟩
  have hml : Scales σ J (col X) m l := by
    have e : m = u⁻¹ * p := by rw [hpm, inv_mul_cancel_left]
    have hp' : (matHom _ σ J p).1 * adMat F (col X) = l.1 • adMat F (col X) := hp
    unfold Scales
    rw [e, map_mul, Units.val_mul, Matrix.mul_assoc, hp', Matrix.mul_smul, unipRad_fix (inv_mem hu)]
  refine ⟨u, hu, m, hm, hpm, hml, hr, fun hl => Subgroup.mem_inf.2 ⟨hm, ?_⟩⟩
  simp only [Subgroup.mem_iInf, Finset.mem_singleton]
  rintro k rfl
  rw [initCols_zero]
  let B : GL (Fin 1) (AF F ⊗[F] E) := ⟨l.1 • 1, (l⁻¹).1 • 1, by simp [smul_smul], by simp [smul_smul]⟩
  refine ⟨B, ?_, sc hml⟩
  have e : Matrix.GeneralLinearGroup.det B = l := Units.ext (by simp [B])
  exact (congrArg (absE F E) e).trans hl

end GlobalTheory.ResLineLevi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

open Filter Topology

variable {D : D7}

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem inBasis_apply {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).1 i j = cpt w ((β⁻¹ * x * β).1 (finCongr h i) (finCongr h j)) := rfl

theorem inBasis_mem_KO {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (hx : x ∈ St β) (w : Pl D.host.E) :
    inBasis rfl β w x ∈ KO (Kw w) (Fin n) := by
  obtain ⟨y, rfl⟩ := hx
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  have hm : ∀ z : GL (Fin n) (Lev.EAf D), z ∈ ({Formalism.L2.DIV.intGL _ _ n y, (Formalism.L2.DIV.intGL _ _ n y)⁻¹} : Set _) →
      ∀ a b, cpt w (z.1 a b) ∈ Formalism.UG.Ov D.host.E w := by
    intro z hz a b
    refine (mem_OA_iff _).1 ?_ w
    rcases hz with rfl | rfl
    · exact (y.1 a b).2
    · rw [← map_inv]; exact ((y⁻¹).1 a b).2
  have e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y := by
    simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  have e2 : β⁻¹ * (Formalism.L2.DIV.frGL β y)⁻¹ * β = (Formalism.L2.DIV.intGL _ _ n y)⁻¹ := by
    rw [← e1]; group
  refine mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [inBasis_apply, e1]; exact hm _ (Or.inl rfl) _ _
  · rw [← map_inv, inBasis_apply, e2]; exact hm _ (Or.inr rfl) _ _

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGlLatCongOfSmul
section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameDepth

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem conj_mem_glLatCong {Λ Λ' : Submodule 𝒪[k] (D → k)} {u : kˣ} (G : GL D k)
    (hG : ∀ x, x ᵥ* G.val ∈ Λ' ↔ x ∈ Λ) {g : GL D k} (hg : g ∈ glLatCong u Λ') :
    G * g * G⁻¹ ∈ glLatCong u Λ := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [← hG, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← vecMul_vecMul, hg.1, hG]
  · have h1 := hg.2 _ ((hG x).2 hx)
    rw [mem_smul_lat] at h1 ⊢
    rw [← hG]
    convert h1 using 1
    rw [Units.smul_def, Units.smul_def, smul_vecMul, vecMul_vecMul, vecMul_vecMul, sub_mul, mul_sub,
      ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, mul_one, one_mul]

theorem vecMul_diagGL_mem (b c d : D → kˣ) (h : ∀ j, d j = b j * c j) (x : D → k) :
    x ᵥ* (diagGL c).val ∈ diagLat d ↔ x ∈ diagLat b := by
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
  rw [diagGL_val, vecMul_diagonal, map_mul, h, Units.val_mul, map_mul]
  exact mul_le_mul_iff_left₀ h0

theorem mem_glLatCong_of_smul {Λ : Submodule 𝒪[k] (D → k)} {u v : kˣ} {g : GL D k}
    (hg : g ∈ glLatCong u (v • Λ)) : g ∈ glLatCong u Λ := by
  have hm : ∀ x, v • x ∈ v • Λ ↔ x ∈ Λ := fun x => by rw [mem_smul_lat, inv_smul_smul]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [← hm, ← hm x, ← hg.1 (v • x), Units.smul_def v x, smul_vecMul, ← Units.smul_def v (x ᵥ* g.val)]
  · have h1 := hg.2 _ ((hm x).2 hx)
    rw [mem_smul_lat, mem_smul_lat] at h1
    rw [mem_smul_lat]
    convert h1 using 1
    rw [smul_comm v⁻¹, Units.smul_def v, smul_vecMul, ← Units.smul_def v, inv_smul_smul]

theorem invT_mem_of_dual {u : kˣ} {c : D → kˣ} {g : GL D k} (hg : g ∈ glLatCong u (dualLat (diagLat c))) :
    invT g ∈ glLatCong u (diagLat c) ∧ gdet (invT g) ∈ unitCong u := by
  rw [dualLat_diagLat] at hg
  have h1 := GlobalTheory.FunObj.GivenAdm.invT_mem_glLatCong (conj_mem_glLatCong (Λ := stdLat k D)
    (diagGL fun j => (c j)⁻¹) (vecMul_diagGL_mem 1 _ _ (by simp)) hg)
  have h2 : invT (diagGL fun j => (c j)⁻¹) = diagGL c := by
    rw [← _root_.inv_inj]
    refine Units.ext ?_
    rw [invT_inv_val, diagGL_val, diagonal_transpose]
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    simp [diagGL_val]
  rw [map_mul, map_mul, map_inv, h2] at h1
  constructor
  · have h3 := conj_mem_glLatCong (Λ := diagLat c) (diagGL c)⁻¹ (fun x => by
      rw [stdLat, ← vecMul_diagGL_mem 1 c c (by simp), vecMul_vecMul, Units.inv_mul, vecMul_one]) h1
    simpa [mul_assoc] using h3
  · have h3 := GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong h1
    rwa [gdet_mul, gdet_mul, show gdet (diagGL c)⁻¹ = (gdet (diagGL c))⁻¹ from map_inv _ _,
      mul_inv_cancel_comm] at h3

theorem HasDepth.mul_glLatCong {A : Type*} {ϖ : kˣ} {e : ℕ} {Λ : Submodule 𝒪[k] (D → k)}
    {Ψ : Matrix A D k → ℂ} (h : HasDepth ϖ e Λ Ψ) {g : GL D k} (hg : g ∈ glLatCong (ϖ ^ e) Λ)
    (Y : Matrix A D k) : Ψ (Y * g.val) = Ψ Y := by
  have hr : ∀ (M : Matrix D D k) i, (Y * M).row i = Y.row i ᵥ* M := fun M i => by
    funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  by_cases hY : Y ∈ matLat A Λ
  · rw [show Y * g.val = Y + Y * (g.val - 1) by rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]]
    exact h.2 _ _ fun i => by rw [hr]; exact hg.2 _ (hY i)
  · rw [h.1 _ hY, h.1 _ fun H => hY fun i => (hg.1 _).1 (by rw [← hr]; exact H i)]

theorem hasDepth_phiA (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype D] [DecidableEq D] (μ : Measure (GL A' k)) [hμ : μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ)
    (ϖ : kˣ) (e : ℕ) (c : D → kˣ) (Ψ : Matrix A' D k → ℂ) (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν)
    (hΨ : HasDepth ϖ e (diagLat c) Ψ) :
    HasDepth ϖ e (latA ϖ e (diagLat c)) (phiA μ σ ν ϖ e (diagLat c) Ψ) := by
  have hlt : valuation k ((ϖ ^ e : kˣ) : k) < 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_lt_one₀ zero_le' (hϖ ▸ uniformizer_lt_one) (by omega)
  have key : ∀ X Z : Matrix A D k, IsPrimFrame (latA ϖ e (diagLat c)) X →
      Z ∈ matLat A (ϖ ^ e • latA ϖ e (diagLat c)) → ∃ κ ∈ glLatCong (ϖ ^ e) (latA ϖ e (diagLat c)),
        X + Z = X * κ.val := by
    rw [latA, dualLat_diagLat, smul_diagLat]
    exact GlobalTheory.PrimFrameMove.exists_glLatCong_move k A D _ _ hlt
  have prim : ∀ X Z : Matrix A D k, IsPrimFrame (latA ϖ e (diagLat c)) X →
      Z ∈ matLat A (ϖ ^ e • latA ϖ e (diagLat c)) → IsPrimFrame (latA ϖ e (diagLat c)) (X + Z) := by
    intro X Z hX hZ
    obtain ⟨κ, hκ, h⟩ := key X Z hX hZ
    rw [h]
    exact GlobalTheory.SplitFlip.Model.isPrimFrame_mul hX κ hκ.1
  refine ⟨fun X hX => if_neg fun h => hX h.2.1, fun X Z hZ => ?_⟩
  by_cases hX : IsPrimFrame (latA ϖ e (diagLat c)) X
  · unfold phiA
    rw [if_pos hX, if_pos (prim X Z hX hZ)]
    obtain ⟨κ, hκ, h⟩ := key X Z hX hZ
    obtain ⟨h1, h2⟩ := invT_mem_of_dual (mem_glLatCong_of_smul hκ)
    obtain ⟨g, rfl⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).1 hX.1
    have h3 : X0 k σ * (invT g).val * κ.val = X0 k σ * (invT (g * invT κ)).val := by
      rw [map_mul, invT_invT, Units.val_mul, Matrix.mul_assoc]
    have hf := @splitTheta_fFun_frameFirstBlock_mul k _ _ _ _ A A' D _ _ _ _ _ _ _ _ μ hμ σ ν Ψ
    rw [h, h3, hf, hf, gdet_mul, map_mul, apow_mul, hν _ h2, apow_of_valuation_eq_one h2.1,
      mul_one, mul_one]
    congr 1
    simp only [smallF, Units.val_mul, ← Matrix.mul_assoc, HasDepth.mul_glLatCong hΨ h1]
  · have hX' : ¬ IsPrimFrame (latA ϖ e (diagLat c)) (X + Z) := fun h => hX (by
      simpa using prim _ (-Z) h (neg_mem hZ))
    unfold phiA
    rw [if_neg hX, if_neg hX']

end GlobalTheory.FrameDepth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MidRangeOfOn
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWMidF

open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

def IsSingChar (T : GL (Fin (n + n)) E) (lam : unipN σ J₂ →* Circle) : Prop :=
  ∃ a : Matrix (Fin n) (Fin n) E, a.det = 0 ∧ ∀ (x : unipN σ J₂) (b : Matrix (Fin n) (Fin n) (AE F E)),
    inBasis σ T (x : UA σ J₂) = blk 1 b 0 1 → (incM F (a.map σ))ᵀ * b * incM F a = 0 → lam x = 1

def IsSing (T : GL (Fin (n + n)) E) (D : UA σ J₂ → ℂ) : Prop :=
  ∀ (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂)), νN.IsHaarMeasure → IsFundamentalDomain (ratN σ J₂) 𝓓 νN →
  ∀ lam : unipN σ J₂ →* Circle, IsRatChar σ lam → ¬ IsSingChar σ T lam → ∀ g, coefN σ νN 𝓓 lam D g = 0

end Defs

def StepCoefOn (R : ℕ → ℕ → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n → R n m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∃ c : ℂ, ∀ (νN : Measure (unipN σ J₂)) (𝓓 : Set (unipN σ J₂)), νN.IsHaarMeasure → IsFundamentalDomain (ratN σ J₂) 𝓓 νN →
  ∀ lam : unipN σ J₂ →* Circle, IsRatChar σ lam → ¬ IsSingChar σ T lam →
  ∀ Φ ∈ kfin σ om K, ∀ g, Cont.HolValueAt (fun s => coefN σ νN 𝓓 lam (fun x => eis σ om K Φ x s) g) (((m : ℂ) - (n : ℂ)) / 2)
    (c * coefN σ νN 𝓓 lam (thetaI σ om ν 𝓕 Φ) g)

def StepOp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ Φ ∈ kfin σ om K,
  ∃ W : Submodule ℂ ((κ → AF F) → ℂ), FiniteDimensional ℂ W ∧ W ≤ kfin σ om K ∧
  ∃ Φ' ∈ W, sec σ om Φ' = sec σ om Φ ∧ thetaI σ om ν 𝓕 Φ' = thetaI σ om ν 𝓕 Φ ∧
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ρ : Measure Ω) (y : Ω → UA σ J₂) (η : Ω → ℂ) (C : Set (UA σ J₂)),
    IsFiniteMeasure ρ ∧ Measurable y ∧ IsCompact C ∧ (∀ ω, y ω ∈ C) ∧ Integrable η ρ ∧
    (∀ D : UA σ J₂ → ℂ, Continuous D → (∀ γ ∈ ratU σ J₂, ∀ g, D (γ * g) = D g) → IsSing σ T D →
      ∀ g, ∫ ω, η ω * D (g * y ω) ∂ρ = 0) ∧
    ∃ L : ℂ → W →ₗ[ℂ] W, (∀ (Ψ : W) (f : Module.Dual ℂ W), Differentiable ℂ fun s => f (L s Ψ)) ∧
      Function.Bijective (L (((m : ℂ) - (n : ℂ)) / 2)) ∧
      (∀ (Ψ : W) (s : ℂ) (g : UA σ J₂), ∫ ω, η ω * flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (sec σ om (Ψ : (κ → AF F) → ℂ)) (((m : ℂ) - (n : ℂ)) / 2) s (g * y ω) ∂ρ =
        flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (sec σ om ((L s Ψ : W) : (κ → AF F) → ℂ)) (((m : ℂ) - (n : ℂ)) / 2) s g) ∧
      ∀ (Ψ : W) (g : UA σ J₂), ∫ ω, η ω * thetaI σ om ν 𝓕 (Ψ : (κ → AF F) → ℂ) (g * y ω) ∂ρ =
        thetaI σ om ν 𝓕 ((L (((m : ℂ) - (n : ℂ)) / 2) Ψ : W) : (κ → AF F) → ℂ) g

def StepConstMid : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ c : ℂ, (∀ Φ ∈ kfin σ om K, ∀ g, Cont.HolValueAt (eis σ om K Φ g) (((m : ℂ) - (n : ℂ)) / 2) (c * thetaI σ om ν 𝓕 Φ g)) → c = 1

def MidCOn (R : ℕ → ℕ → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n → R n m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∃ c : ℂ, ∀ Φ ∈ kfin σ om K, ∀ g, Cont.HolValueAt (eis σ om K Φ g) (((m : ℂ) - (n : ℂ)) / 2) (c * thetaI σ om ν 𝓕 Φ g)

def MidOn (R : ℕ → ℕ → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n → R n m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ g, Cont.HolValueAt
    (fun s => Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (fun g => om (1, g) Φ 0)
        (((m : ℂ) - (n : ℂ)) / 2) s) g)
    (((m : ℂ) - (n : ℂ)) / 2) ((if n < m then 1 else 2 : ℂ) * ⨍ h in 𝓕, thetaSum F (om (h, g) Φ) ∂ν)

end GlobalTheory.SWMidF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorProductFockVectorExtremalTorusWeight
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.MinorWeightCore

open GlobalTheory.JointHarm GlobalTheory.AdTh.MinorWeight

theorem delta_extremal_weight_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (τ : D.what₂.Tau) (a : Fin (Wc D i).rank → ℝ) (t : T0), R.ωP i t (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * diagonal (fun j => cexp ((a j : ℂ) * I)) * (R.MW i (sg0 D A)).fr τ)) (R.ptP i t (RealDat.Delta i)) = cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • R.ptP i t (RealDat.Delta i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i hV τ a t
  have hA := GlobalTheory.PairWeightArith.arithAt D i
  have hI := GlobalTheory.PairInfTypes.infTypesAt D T0 R.toLevCh A.μ0 h.lev i t
  have hε := h.models.order i
  have hθ := h.models.inf
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.JointHarm.weights_of_minors D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) hε
  have hpq : ∀ ρ, ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = (Wc D i).rank := fun ρ =>
    (hA ρ).rank.1.trans (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).symm
  have hmn : (Wc D i).rank ≤ (Vc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le.trans (r_le_V i)
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := pure_one _ (R.vP i t) ▸ h.thP.pt_theta i t 1
  have hv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.thP.vP i t) hth
  have hB : ∀ ρ, (R.BV i ρ)ᴴ * gramAt D (Vc D i) ρ * R.BV i ρ = 1 := fun ρ => by
    obtain ⟨e, he, h1, -⟩ := h.models.BV i ρ
    rw [h1, ← diagonal_one]
    congr 1
    funext j
    rcases he j with hj | hj
    · rw [hj.1]; rfl
    · exact absurd j.2 (not_lt.2 hj.2)
  have hBi : ∀ ρ, (R.BV i ρ)⁻¹ * R.BV i ρ = 1 := fun ρ =>
    Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_left_inverse (hB ρ))
  unfold RealDat.ptP
  generalize R.MW i (sg0 D A) = M at hε hx hv ⊢
  have h1 : ∀ ρ, M.fr ρ * (M.fr ρ)⁻¹ = 1 := fun ρ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))
  have hK := diag_mem (ε := M.ε τ) a
  obtain ⟨a1, a2, a3⟩ := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (conj_mem M τ hK)
  generalize atTau R.θ (Wc D i) τ _ = g at a1 a2 a3 ⊢
  let θs : D.what₂.Tau → Fin (Wc D i).rank → ℝ := fun ρ => if ρ = τ then a else 0
  have hg : ∀ ρ, M.fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) * (M.fr ρ)⁻¹ =
      diagonal fun j => cexp ((θs ρ j : ℂ) * I) := fun ρ => by
    by_cases e : ρ = τ
    · subst e
      rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) = _ from a2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1,
        Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
      simp only [θs, if_true]
    · rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i) g) = _ from a3 ρ e, Matrix.mul_one, h1]
      simp [θs, e]
  have e1 : ∀ ρ, (R.BV i ρ)⁻¹ * compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * R.BV i ρ = 1 := fun ρ => by
    rw [show compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) = 1 from GlobalTheory.PointAtPlaceHom.infMat_one _ _, Matrix.mul_one, hBi]
  have key := (GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ _ _ _ _ _ _ M (R.BV i) (h.thP.ωP i t) hθ (D.sp.V_sig _) (D.sp.W_sig _) hB _ _ hpq hε
    _ _ (fun ρ => (hI ρ).chiV) (fun ρ => (hI ρ).chiW) x₁ x₂ x₃ (fun ρ => (hx ρ).1) (fun ρ => (hx ρ).2.1)
    (fun ρ => (hx ρ).2.2.1) _ hth hv 1 (one_mem _) g a1 (fun ρ => hg ρ ▸ diag_mem _)).2 (RealDat.Delta i)
  simp only [hg, e1] at key
  rw [key, RealDat.Delta, fact_diagonal M.ε _ _ _ _ x₁ x₂ x₃ hmn hpq hε (fun ρ => (hA ρ).aPlus_antitone) (fun ρ => (hA ρ).aM_anti)
    _ (fun _ _ => Complex.exp_ne_zero _), map_smul]
  congr 1
  rw [Finset.prod_eq_single τ (fun ρ _ e => by simp [θs, e]) (fun e => (e (Finset.mem_univ _)).elim), Complex.ofReal_sum,
    Finset.sum_mul, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hr := revNeg_shape (Nat.le.intro (hpq τ)) (hε τ) j
  have hj := j.2
  rw [extWt, (hx τ).2.2.2.1, ← Complex.exp_int_mul, wtK, hr]
  congr 1
  by_cases hp : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1
  · simp [θs, hp, mul_assoc]
  · rw [if_neg hp, if_neg hp, if_neg (by have := hpq τ; omega),
      show (Wc D i).rank - 1 - ((Wc D i).rank - 1 - (j - ((Wc D i).sig (tauE D τ)).1)) =
        j - ((Wc D i).sig (tauE D τ)).1 by omega]
    simp [θs, mul_assoc]

end GlobalTheory.AdTh.MinorWeightCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpanStatement
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_omega_finite_free_and_p_sq_mem_dlog_span : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), v.Integers O → GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ G : PDivGroup p O, Module.Finite O G.omega ∧ Module.Free O G.omega ∧ ∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G))) := by
  first | exact @GlobalTheory.DlogSpan.finite_free_and_sq_smul_mem_span | exact GlobalTheory.DlogSpan.finite_free_and_sq_smul_mem_span | (intros; apply GlobalTheory.DlogSpan.finite_free_and_sq_smul_mem_span <;> assumption)
end

