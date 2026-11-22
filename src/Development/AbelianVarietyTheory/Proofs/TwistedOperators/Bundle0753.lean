import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameLatticeFunctional
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0740
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0730
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0731
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0732
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0744
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameLatticeFunctionalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_frame_lattice_functional : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k)
    (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank)) (ϖ : 𝒪[k]),
  p.v = v → Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} →
  ∀ a ∈ (pcFB W F σ h h').A₁, ∀ (q : Fin (σ + 1)) i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v,
    (z : k) = (ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)) * (p.pr (incA D (-D.host.xi0)))⁻¹ ^ (q.1 + 1) *
      (β.b' *ᵥ fun j => p.pr (a j q)) i := by
  first | exact @GlobalTheory.DepthColumn.col_mem_depth | exact GlobalTheory.DepthColumn.col_mem_depth | (intros; apply GlobalTheory.DepthColumn.col_mem_depth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseIdealsCompletionEqOfModulusUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.StairIdealAt

theorem completion_eq_of_modul_unit : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (ρ : ℕ) (v : GlobalTheory.FinPl.Pl D), 0 < ρ → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v → (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹) ≠ 0) ∧ (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹) ≠ 0) ∧ ∀ s, s ∈ GlobalTheory.SeeSaw.idV ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹))⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹))⁻¹) v := by
  intro D T L P sc ρ v hρ hM
  have hx : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hAb : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hMo : ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.modul_ne_bot sc
  have hS : P.stA sc ≠ 0 := ((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc).1
  have hT : P.stAbar sc ≠ 0 := mul_ne_zero hAb (inv_ne_zero hMo)
  have e1 : ρ - 1 + 1 = ρ := by omega
  have e2 : 2 * ρ - (ρ - 1) = ρ + 1 := by omega
  have hneg : ∀ k : ℕ, FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((-D.host.xi0) ^ k)⁻¹ =
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ^ k)⁻¹ := by
    intro k
    rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_pow]
    congr 1
    congr 1
    apply FractionalIdeal.spanSingleton_eq_spanSingleton.2
    refine ⟨-1, ?_⟩
    rw [Units.smul_def]
    simp
  rw [e1, e2, hneg, hneg]
  set X := FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 with hXdef
  have hX : X ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hx
  refine ⟨mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX)) (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT))),
    mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX)) (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT))), ?_⟩
  have key : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) * ((X ^ ρ)⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ ρ)⁻¹))⁻¹ *
      ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ =
      FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * ((X ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹))⁻¹ := by
    rw [← FractionalIdeal.spanSingleton_inv, ← hXdef]
    have hTd : P.stAbar sc = D.host.AAbar * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := rfl
    rw [hTd]
    simp only [mul_inv, inv_inv, pow_succ, mul_pow]
    calc _ = (X⁻¹ * X) * (D.host.AAbar * ((X ^ ρ) * ((P.stA sc ^ ρ * P.stA sc)⁻¹ * ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) ^ ρ *
          (((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) ^ ρ))) * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) := by
          rw [inv_mul_cancel₀ hX, one_mul, mul_inv]
      _ = _ := by ring
  have hB0 : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) * ((X ^ ρ)⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ ρ)⁻¹))⁻¹ ≠ 0 :=
    mul_ne_zero hAb (inv_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX))
      (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT)))))
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.IdVGen.idV_gen D v _ hB0
  have h1 := GlobalTheory.Core.Mi.LatMatch.DiUnit.eq_one_iff.1 (GlobalTheory.Core.Mi.LatMatch.DiUnit.inv_eq_one hM)
  have hp := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v _ _ y 1 hy0 one_ne_zero hy h1
  rw [mul_one, key] at hp
  intro s
  rw [hp, hy]

end GlobalTheory.StairIdealAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.StairLine

variable {D : D7}

open GlobalTheory.SeeSaw

theorem incA_mul_mem_idV {𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} (x : D.host.E) {t : AE D} (ht : t ∈ idV 𝔟 v) :
    incA D x * t ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔟) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hy
    rw [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul]
    exact GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv
      (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ x) hb)
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy

theorem mem_idV_inv_mul {𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} {x : D.host.E} (hx : x ≠ 0) (s : AE D) :
    s ∈ idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟) v ↔ incA D x * s ∈ idV 𝔟 v := by
  constructor
  · intro h
    have := incA_mul_mem_idV x h
    rwa [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hx,
      FractionalIdeal.spanSingleton_one, one_mul] at this
  · intro h
    have := incA_mul_mem_idV x⁻¹ h
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul] at this

theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (hp : 2 * p.1 + 1 ≠ c) :
    (d.aᴴ * B.gram * d.a) ⟨c - 1 - p.1, by omega⟩ = Pi.single p 1 ∧
      (d.aᴴ * B.gram * frameMat B A d.ι) = 0 := by
  refine ⟨?_, ?_⟩
  · have e := d.gram
    change d.aᴴ * B.gram * d.a = _ at e
    rw [e]
    funext q
    simp only [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix, Pi.single_apply, Fin.ext_iff]
    have := p.2; have := q.2
    by_cases hq : q.1 = p.1
    · rw [if_pos (by omega), if_neg (by omega), if_pos hq]
    · rw [if_neg (by omega), if_neg hq]
  · have e := d.perp
    change (frameMat B A d.ι)ᴴ * B.gram * d.a = 0 at e
    have hg : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq (B.frame j) (B.frame i)
    have := congrArg Matrix.conjTranspose e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hg,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at this

theorem line_mem {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FI D) (v : GlobalTheory.FinPl.Pl D) (p : Fin c) (hp : 2 * p.1 + 1 ≠ c) (t : AE D) :
    (fun k => t * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ t ∈ idV (𝔟 p) v := by
  classical
  obtain ⟨hf1, hf2⟩ := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero d p hp
  generalize (⟨c - 1 - p.1, by omega⟩ : Fin c) = q at hf1
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin B.rank → D.host.E, φ = (d.aᴴ * B.gram) q := ⟨_, rfl⟩
  have hφa : ∀ u : Fin c → D.host.E, φ ⬝ᵥ (d.a *ᵥ u) = u p := by
    intro u
    rw [Matrix.dotProduct_mulVec, hφ]
    have : (d.aᴴ * B.gram) q ᵥ* d.a = (d.aᴴ * B.gram * d.a) q := rfl
    rw [this, hf1]
    simp [Pi.single_apply, dotProduct]
  have hφM : ∀ y, φ ⬝ᵥ (frameMat B A d.ι *ᵥ y) = 0 := by
    intro y
    rw [Matrix.dotProduct_mulVec, hφ]
    have : (d.aᴴ * B.gram) q ᵥ* frameMat B A d.ι = (d.aᴴ * B.gram * frameMat B A d.ι) q := rfl
    rw [this, hf2]
    exact zero_dotProduct y
  have h3 : ∑ l, φ l * d.a l p = 1 := by
    have := congrFun hf1 p
    rw [Pi.single_eq_same, Matrix.mul_apply] at this
    rw [hφ]; exact this
  let Φ : (Fin B.rank → AE D) →+ AE D :=
    { toFun := fun z => ∑ l, incA D (φ l) * z l
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib] }
  constructor
  · intro h
    have hle : latV B (d.lat Λ 𝔟) (· = v) ≤ (idV (𝔟 p) v).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, hαv, a', ha', x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at ha'
      subst ha'
      obtain ⟨y, -, u, hu, rfl⟩ := hx
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show ∑ l, incA D (φ l) * _ ∈ _
      simp only [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_sum]
      have : ∑ l, φ l * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) l = u p := by
        have h1 := hφa u
        have h2 := hφM y
        rw [← h1, ← add_zero (φ ⬝ᵥ (d.a *ᵥ u)), ← h2, ← dotProduct_add, add_comm]
        rfl
      rw [this]
      exact GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv (hu p)
    have h2 : Φ (fun k => t * incA D (d.a k p)) ∈ idV (𝔟 p) v := hle h
    have e : Φ (fun k => t * incA D (d.a k p)) = t := by
      show ∑ l, incA D (φ l) * (t * incA D (d.a l p)) = t
      calc ∑ l, incA D (φ l) * (t * incA D (d.a l p)) = t * incA D (∑ l, φ l * d.a l p) := by
            rw [map_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_mul, mul_left_comm]
        _ = t := by rw [h3, map_one, mul_one]
    rwa [e] at h2
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hs
      refine AddSubgroup.subset_closure ⟨α, hα, hαv, 1, rfl, d.a *ᵥ Pi.single p b,
        ⟨0, Λ.zero_mem, Pi.single p b, fun r => ?_, by simp⟩, ?_⟩
      · by_cases hr : r = p
        · subst hr; simpa using hb
        · rw [Pi.single_eq_of_ne hr]; exact (𝔟 r).zero_mem
      · funext k
        rw [mul_comm, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    | zero =>
      convert (latV B (d.lat Λ 𝔟) (· = v)).zero_mem using 1
      funext k; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      funext k; simp [add_mul]
    | neg x _ hx =>
      convert neg_mem hx using 1
      funext k; simp [neg_mul]

open GlobalTheory.ChiGrid in

theorem colMul_dJ_mem_iff : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ), ∀ a ∈ idAt D (· = v), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔ a ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (G.pl.stA sc ^ (2 * ρ - i.1) * (G.pl.stAbar sc ^ (i.1 + 1))⁻¹)) v := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h v i a ha
  obtain ⟨hc, he, -⟩ := hF.hJ ρ h
  have hx : ((-D.host.xi0) ^ (i.1 + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a = fun k => (incA D ((-D.host.xi0) ^ (i.1 + 1)) * a) *
      incA D ((G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) i)) := by
    funext k
    show a * incA D ((F.dJ ρ h).e k i) = _
    rw [he]
    show a * incA D ((-D.host.xi0) ^ (i.1 + 1) * _) = _
    rw [map_mul, ← mul_assoc, mul_comm a]
  have e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat _ _ _
  have hi := i.2
  rw [e1, e2, line_mem _ _ _ v _ (by simp only [Fin.val_castLE]; omega), mem_idV_inv_mul hx]
  simp only [stairId, Fin.val_castLE, Nat.add_sub_cancel]

end GlobalTheory.StairLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFramesSuccessiveLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.GoodFB

theorem mxAt_mul {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {a : Mx D m n} (ha : MxAt P a) (b : Mx D n k) :
    MxAt P (a * b) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem mxAt_mul_left {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (b : Mx D m n) {a : Mx D n k} (ha : MxAt P a) :
    MxAt P (b * a) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (ha l j)

theorem goodAt_stdAt_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.core (2 * σ + 3))) (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v ∧ StdAt (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  intro D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hQ T L μ0 hL sc G W M hM F hF
  have t1 := GlobalTheory.T.psi_primitive_standardFrames_fourierJacobiLevel D hQ T L μ0 hL sc G W M hM F hF (σ + 1) h v hv
  have t2 := GlobalTheory.T.fourierJacobiStep_basePoint_columns_primitive D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have r1 := GlobalTheory.T.depthLatticeGridRow_local_eq_completed_homLattice D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  have r2 := GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v
  have r3 := GlobalTheory.T.selfDualHomLatticeModulusShift_local_eq_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  obtain ⟨-, hb, -⟩ := I
  have hbσ := hb σ h'
  have hbσ1 := hb (σ + 1) h
  refine ⟨⟨?_, ?_, ?_, hbσ.1, (hbσ1.2.1 v).2, (hbσ.2.1 v).1, t1, t2⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (G.sp.V_is (2 * σ + 3) 0 (by omega) (by omega) (by omega)).sd
  · exact (G.sp.P_is (2 * σ + 3) (by omega)).sd
  · exact (G.sp.V_is (2 * σ + 2) 0 (by omega) (by omega) (by omega)).sd
  · intro a ha
    exact r1 _ (mxAt_mul ha _)
  · intro a ha
    obtain ⟨⟨ε, hεε, -, hεi, -, hεoff⟩, -⟩ := GlobalTheory.FinPl.localComponents D (· = v)
    refine ⟨ε • a, fun i j => ?_, ?_⟩
    · rw [hεoff]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_sub, ← mul_assoc, hεε, sub_self]
    · have := r2 ε hεi _ ha
      have e : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (ε • a) =
          ε • (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) a := by
        rw [HypDec.extX_apply, HypDec.extX_apply, Matrix.smul_mul]
      rw [e]
      exact this
  · intro ξ hξ
    exact r3 _ (mxAt_mul (mxAt_mul_left _ hξ) _)

end GlobalTheory.AscFin.GoodFB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalCuspidalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_diagonal_cuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt R.θ (G.P (i + 1)).V τ ((G.P (i + 1)).S τ) (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  first | exact @GlobalTheory.ThetaLiftTypeUp.lift_hasTypeAt | exact GlobalTheory.ThetaLiftTypeUp.lift_hasTypeAt | (intros; apply GlobalTheory.ThetaLiftTypeUp.lift_hasTypeAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsOfFlatMapWeilActionNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingConditions_of_flatMap_weilAction_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, ∀ h, flatS dV dW s (rat x₀) y (s.om (1, h) Φ) ≠ 0 → Cond dW p (rat x₀) y ψ (fun _ => True) h := by
  first | exact @GlobalTheory.AscFinCond.cond_of_flatS_ne | exact GlobalTheory.AscFinCond.cond_of_flatS_ne | (intros; apply GlobalTheory.AscFinCond.cond_of_flatS_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumScalarsEqProductEdgeFactorsRow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVacScalar

private theorem map_mt_one_eq_one {D : D7} (V : HSp D) : (Formalism.L2.Theta.mt V 1).map (finPart D) = 1 := by
  rw [Formalism.L2.Theta.mt, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem scalars_eq_edgeFactors : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)),
    finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ (c₁ c₂ : ℂ),
    W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) →
    W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m) →
    c₁ * c₂ = ∏ w : locPl G t, ((oppositePath D.R.m).map ((locGrid G t w.1).edgeFactor .one (Pi.mulSingle (j + 1, D.R.m)
      (inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
        (finG (G.V (.grid (j + 1) D.R.m)) k))))).prod := by
  intro D T L sc G W U S μ₀ hL t ht j hj k hk c₁ c₂ h₁ h₂
  obtain ⟨hA, hB, hC, hD⟩ := GlobalTheory.RowMovedLat.moved_pair_stab S ht j hj k hk
  have e₁ := GlobalTheory.RowVacScalar.vacScalar_eq_prod S hL t j hj.le _ hA ?g₁ hB ?l₁ c₁ h₁
  have e₂ := GlobalTheory.RowVacScalar.vacScalar_eq_prod S hL t (j + 1) hj _ ?g₂ hC ?l₂ hD c₂ h₂
  · rw [e₁, e₂, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact GlobalTheory.T.splitPlaceScalars_mul_eq_oppositePath_edgeFactors S ht j hj k hk w.1 w.2 ⟨_, GlobalTheory.RowVacScalar.isIdemAt_idemAt hL G t w.2⟩
  case g₁ =>
    dsimp only [GridData.toPair]
    exact one_mem _
  case l₁ =>
    intro y
    dsimp only [GridData.toPair]
    rw [map_mt_one_eq_one, Matrix.one_mulVec]
  case g₂ =>
    dsimp only [GridData.toPair]
    rw [map_one]
    exact one_mem _
  case l₂ =>
    intro y
    dsimp only [GridData.toPair]
    rw [map_one, map_mt_one_eq_one, Matrix.one_mulVec]

end GlobalTheory.RowVacScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_split_place_indicator : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @GlobalTheory.SplitScalar.scalar_eq_one_split | exact GlobalTheory.SplitScalar.scalar_eq_one_split | (intros; apply GlobalTheory.SplitScalar.scalar_eq_one_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationAAModulusDivConjLeCosetExponentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_AA_modulusDivConj_le_cosetExponent : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc), ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  first | exact @GlobalTheory.AscFin.ShiftVal.val_le_cosExp | exact GlobalTheory.AscFin.ShiftVal.val_le_cosExp | (intros; apply GlobalTheory.AscFin.ShiftVal.val_le_cosExp <;> assumption)
end

