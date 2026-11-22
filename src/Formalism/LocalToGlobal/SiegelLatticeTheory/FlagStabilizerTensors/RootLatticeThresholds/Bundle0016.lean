import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0005
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BuiltPf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Built

open Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def chiStd (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem isCut0_chiStd : Formalism.FourierDecayAlt.C6.IsCut0 chiStd := by
  unfold Formalism.FourierDecayAlt.C6.IsCut0
  refine ⟨?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · show ContDiff ℝ _ (Real.smoothTransition ∘ fun x : ℝ => 2 * x - 1)
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

section tower

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def towerOf (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.LevTower k r Wp Wq :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose

theorem towerOf_base (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : (towerOf B h1 h2 h3).base = B :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.1

theorem towerOf_norm (B : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (h1 : B.μW Set.univ = 1) (h2 : B.μW' Set.univ = 1)
    (h3 : B.μN = Formalism.FourierDecayAlt.D.muN k r) : Formalism.FourierDecayAlt.D.TowerNormalised (towerOf B h1 h2 h3) :=
  (Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq B h1 h2 h3).choose_spec.2

end tower

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

abbrev par (I : CarrierIn X u u') (v : Fin I.nf) : Formalism.FourierDecayAlt.M.Par := Formalism.FourierDecayAlt.D.parOf (sOf I) v

def sgOf {nf : ℕ} (G : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (pl : Fin nf ≃ InfinitePlace D.host.E)
    (T T' : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (v : Fin nf) : ℂ :=
  Formalism.FourierDecayAlt.M.sgn ⟨G.k, G.r, T, T', (G.place (pl v)).u de, (G.place (pl v)).u de'⟩ l

theorem sg_of (I : CarrierIn X u u')
    (h : I.sg = sgOf I.G I.pl ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) I.de I.de' (I.l + 1)) :
    ∀ v, I.sg v = Formalism.FourierDecayAlt.M.sgn (par I v) ((sOf I).l + 1) := by
  intro v
  rw [h]
  rfl

def ParNums (I : CarrierIn X u u') : Prop :=
  ∀ v, (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u i - (par I v).u 1 = n) ∧
    (∀ i ∈ Finset.Icc 1 (par I v).k, ∃ n : ℤ, (par I v).u' i - (par I v).u 1 = n) ∧
    ∀ i ∈ Finset.Icc 1 ((par I v).k - 1), (par I v).lo i ≤ (par I v).hi i

def Types (I : CarrierIn X u u') : Prop :=
  ∀ v, Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z (I.T v).base.π (par I v).u ∧
    Formalism.FourierDecayAlt.Q.IsType I.G.k I.G.r (I.T v).base.z' (I.T v).base.π' (par I v).u'

def Frames (I : CarrierIn X u u') : Prop := ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame (I.T v).base (I.ν' v) (I.m₀ v)

def CoefCC (I : CarrierIn X u u') : Prop := ∀ v (m : ℕ), Formalism.FourierDecayAlt.B.InCC I.A₀ m (I.fc v)

def CoefCap (I : CarrierIn X u u') : Prop :=
  ∀ v (Y : ℝ), ∀ g ∈ Formalism.FourierDecayAlt.B.GV I.G.k I.G.r,
    Formalism.FourierDecayAlt.Q.CV I.G.k I.G.r (Y : ℂ) (I.fc v) g = (((sOf I).P v Y : ℝ) : ℂ) • I.fc v g

theorem isPlace_of (I : CarrierIn X u u') (hN : ParNums I) (hty : Types I) (v : Fin I.nf) :
    Formalism.FourierDecayAlt.Q.IsPlace (par I v) (I.T v).base.z (I.T v).base.z' (I.T v).base.π (I.T v).base.π' := by
  unfold Formalism.FourierDecayAlt.Q.IsPlace
  obtain ⟨h1, h2, h3⟩ := hN v
  obtain ⟨t1, t2⟩ := hty v
  obtain ⟨e1, e2⟩ := I.hT v
  have p1 := (I.T v).base.T_pos
  have p2 := (I.T v).base.T'_pos
  rw [e1] at p1
  rw [e2] at p2
  exact ⟨⟨(I.T v).base.k_pos, p1, p2, h1, h2, h3⟩, (I.T v).base.z_mem, (I.T v).base.z'_mem, e1, e2, t1, t2⟩

def FramesExist : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (I : CarrierIn X u u') (Mo : ModelsFor (sOf I))
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k), (CarrierOf I Mo).FromX → (∀ v, i0 v = i0' v) →
    ∃ (ν' : Fin I.nf → Fin (2 * I.G.r + I.G.k + 1) → ℂ) (m₀ : Fin I.nf → Formalism.FourierDecayAlt.B.Mat I.G.k I.G.r),
      Formalism.L2.SG.RealObj.BaseFromX X (sOf I) u u' i0 i0' I.τ I.Q I.Qi ν' m₀ ∧
        ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame (I.T v).base (ν' v) (m₀ v)

end Formalism.L2.SG.Pf.Built
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyConst
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.EnergyConst

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

def e1 (D : D7) : ℕ := (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) / 3

def rdExp (D : D7) : ℕ := 2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) + e1 D

def Anum (D : D7) : ℝ := D.host.rdE ^ rdExp D * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (3 * (D.R.rS + 1))

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Kexp (P : Parts X u u') : ℝ := Anum D / P.Gam0

variable (X u u') in

def LemmaMS (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Prop :=
  (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p =
    D.host.rdE ^ (D.R.f * e1 D) * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) *
      (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ

theorem anum_pow : Anum D ^ D.R.f =
    Formalism.L2.SG.MassDataConc.kapN D * (D.host.rdE ^ (D.R.f * e1 D) *
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3)))) := by
  have hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS
    exact Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have key : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) =
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (2 * D.R.f * D.R.rS * (D.R.rS + 1)) *
        ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (3 * (D.R.rS + 1) * D.R.f) := by
    rw [← pow_add]
    congr 1
    ring
  rw [key]
  simp only [Anum, rdExp, Formalism.L2.SG.MassDataConc.kapN]
  rw [mul_pow, ← pow_mul, ← pow_mul]
  field_simp
  ring

theorem rdE_pos' : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.rpow_pos_of_pos
  have h := NumberField.discr_ne_zero (K := D.host.E)
  exact abs_pos.mpr (by exact_mod_cast h)

theorem energy_constant_nonneg (P : Parts X u u') : 0 ≤ P.Gam0 := by
  unfold Formalism.L2.SG.Pf.Carrier.Parts.Gam0 Formalism.FourierDecayAlt.D.GamLev
  apply Finset.prod_nonneg
  intro l _
  apply div_nonneg
  · apply zpow_nonneg
    unfold Formalism.FourierDecayAlt.D.kapG Formalism.FourierDecayAlt.S6.rd
    positivity
  · unfold Formalism.FourierDecayAlt.D.deG Formalism.FourierDecayAlt.S6.rd
    positivity

theorem constPin_of (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : LemmaMS X u u' ψ)
    (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f) :
    ConstPin P ψ (fun _ => Kexp P) := by
  obtain ⟨-, -, -, -, -, -, hZZ, hPP, -⟩ := hC
  have hb : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS
    exact Nat.cast_ne_zero.mpr (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hrd : 0 < D.host.rdE := rdE_pos'
  have hA : 0 ≤ Anum D := by
    unfold Anum
    exact mul_nonneg (pow_nonneg hrd.le _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hK0 : 0 ≤ Kexp P := div_nonneg hA (energy_constant_nonneg P)
  refine ⟨fun _ => hK0, ?_⟩
  have hfS : P.S.f = D.R.f := by
    rw [← hf, ← Fintype.card_fin P.S.f]
    exact Fintype.card_congr P.τ
  have hprod : ∏ _v : InfinitePlace X.B.I.F, Kexp P = Anum D ^ D.R.f / P.Gam0 ^ D.R.f := by
    rw [Finset.prod_const, Finset.card_univ, hf, Kexp, div_pow]
  have hvZZ : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ := hZZ
  have hvPP : 0 < (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP := by
    show 0 < ∏ l : Fin (D.R.rS + 1), ∏' v : Formalism.L2.SG.LocVol.PlX X, Formalism.L2.SG.LocVol.PPX X u u' ψ l v
    exact Finset.prod_pos (fun l _ => (hPP l).2)
  have hkap : Formalism.L2.SG.MassDataConc.kapN D ≠ 0 := by
    unfold Formalism.L2.SG.MassDataConc.kapN
    exact mul_ne_zero (pow_ne_zero _ hrd.ne') (inv_ne_zero (pow_ne_zero _ hb))
  have hM : D.host.rdE ^ (D.R.f * e1 D) *
      ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * ((D.R.rS + 1) * (2 * D.R.rS + 3))) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hrd.ne') (pow_ne_zero _ hb)
  rw [hprod, anum_pow, hMS, hfS]
  field_simp

end Formalism.L2.SG.Pf.Carrier.EnergyConst
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPfLoc
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPfLoc

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
open Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gram

variable {α V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem inner_lc (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) (c d : α →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ f c, Finsupp.linearCombination ℂ f d⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ g c, Finsupp.linearCombination ℂ g d⟫_ℂ := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, h]

theorem norm_lc (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) (c : α →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ f c‖ = ‖Finsupp.linearCombination ℂ g c‖ := by
  have hsq : ‖Finsupp.linearCombination ℂ f c‖ ^ 2 = ‖Finsupp.linearCombination ℂ g c‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, inner_lc f g h c c]
  have := congrArg Real.sqrt hsq
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

theorem exists_linearIsometryEquiv_of_inner_eq (f g : α → V) (h : ∀ a b, ⟪f a, f b⟫_ℂ = ⟪g a, g b⟫_ℂ) :
    ∃ U : V ≃ₗᵢ[ℂ] V, ∀ a, U (f a) = g a := by
  classical
  set F := Finsupp.linearCombination ℂ f with hF
  set G := Finsupp.linearCombination ℂ g with hG
  have hker : LinearMap.ker F ≤ LinearMap.ker G := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have := norm_lc f g h c
    rw [← hF, ← hG, hc, norm_zero] at this
    exact norm_eq_zero.1 this.symm
  let φ : LinearMap.range F →ₗ[ℂ] V :=
    ((LinearMap.ker F).liftQ G hker).comp F.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ c, φ ⟨F c, LinearMap.mem_range_self F c⟩ = G c := by
    intro c
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hφn : ∀ x, ‖φ x‖ = ‖x‖ := by
    rintro ⟨_, c, rfl⟩
    rw [hφ c]
    show ‖G c‖ = ‖F c‖
    exact (norm_lc f g h c).symm
  let L : LinearMap.range F →ₗᵢ[ℂ] V := { φ with norm_map' := hφn }
  refine ⟨L.extend.toLinearIsometryEquiv rfl, fun a => ?_⟩
  have hfa : f a ∈ LinearMap.range F := ⟨Finsupp.single a 1, by simp [hF]⟩
  have e1 : (L.extend.toLinearIsometryEquiv rfl) (f a) = L.extend (f a) := rfl
  rw [e1, show f a = ((⟨f a, hfa⟩ : LinearMap.range F) : V) from rfl, LinearIsometry.extend_apply]
  have e2 : (⟨f a, hfa⟩ : LinearMap.range F) =
      ⟨F (Finsupp.single a 1), LinearMap.mem_range_self F _⟩ := by
    ext; simp [hF]
  rw [e2]
  show φ _ = g a
  rw [hφ]
  simp [hG]

end Gram

section Loc

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem wu_ne (u : D.what₂.Word) : ∃ x0, X.Wu u x0 ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 := (X.Wu_spec u).2.2.2.2
  simp [hc] at h1

open Classical in
theorem inner_upd (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (x0 : X.B.I.Ginf)
    (y y' : Formalism.REAL.UJ (X.B.I.ε v)) :
    ⟪X.Wu u (Function.update x0 v y), X.Wu u (Function.update x0 v y')⟫_ℂ =
      ⟪X.Wloc u v y, X.Wloc u v y'⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪X.Wloc u w (x0 w), X.Wloc u w (x0 w)⟫_ℂ := by
  rw [X.Wu_tens, X.Wu_tens, X.tensU_inner, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw), Function.update_of_ne (Finset.ne_of_mem_erase hw)]

open Classical in

theorem wloc_gram (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s)) (a b : Formalism.REAL.UJ (X.B.I.ε v)) :
    ⟪X.Wloc u v (s * a), X.Wloc u v (s * b)⟫_ℂ = ⟪X.Wloc u v a, X.Wloc u v b⟫_ℂ := by
  obtain ⟨x0, hx0⟩ := wu_ne X u
  set S : X.B.I.Ginf := Function.update 1 v s with hSdef
  have hS : S ∈ X.SinfU u := by
    intro w
    by_cases hw : w = v
    · subst hw
      simpa [S] using hs
    · simp only [S, Function.update_of_ne hw, Pi.one_apply]
      refine ⟨fun a => ?_, ?_⟩ <;> simp [uMat]
  have hmul : ∀ y, S * Function.update x0 v y = Function.update x0 v (s * y) := by
    intro y
    funext w
    by_cases hw : w = v
    · subst hw
      simp [S]
    · simp [S, Function.update_of_ne hw]
  have hW : ∀ x, X.Wu u (S * x) = X.psiInfU u S • X.piU u S (X.Wu u x) := fun x => (X.Wu_spec u).1 S hS x
  have hU : ∀ x y, ⟪X.piU u S x, X.piU u S y⟫_ℂ = ⟪x, y⟫_ℂ := (X.piU_rep u).2.2.1 S hS
  have hψ : conj (X.psiInfU u S) * X.psiInfU u S = 1 := by
    rw [Complex.conj_mul', Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u S]
    simp
  have key : ∀ y y', ⟪X.Wu u (S * Function.update x0 v y), X.Wu u (S * Function.update x0 v y')⟫_ℂ =
      ⟪X.Wu u (Function.update x0 v y), X.Wu u (Function.update x0 v y')⟫_ℂ := by
    intro y y'
    rw [hW, hW, inner_smul_left, inner_smul_right, hU, ← mul_assoc, hψ, one_mul]
  have hK : (∏ w ∈ Finset.univ.erase v, ⟪X.Wloc u w (x0 w), X.Wloc u w (x0 w)⟫_ℂ) ≠ 0 := by
    have h0 := inner_upd X u v x0 (x0 v) (x0 v)
    rw [Function.update_eq_self] at h0
    have hne : ⟪X.Wu u x0, X.Wu u x0⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx0
    rw [h0] at hne
    exact right_ne_zero_of_mul hne
  have h2 := key a b
  rw [hmul, hmul, inner_upd, inner_upd] at h2
  exact mul_right_cancel₀ hK h2

theorem wloc_unit (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s)) :
    ∃ A : X.Vloc u v ≃ₗᵢ[ℂ] X.Vloc u v, ∀ x, X.Wloc u v (s * x) = (1 : ℂ) • A (X.Wloc u v x) := by
  obtain ⟨A, hA⟩ := exists_linearIsometryEquiv_of_inner_eq (fun x => X.Wloc u v x) (fun x => X.Wloc u v (s * x))
    (fun a b => (wloc_gram X u v s hs a b).symm)
  exact ⟨A, fun x => by rw [one_smul, hA x]⟩

theorem hilbertSchmidt_sq_nonneg {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) : 0 ≤ hs2 A := by
  unfold Formalism.L2.SG.RealObj.hs2
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem hilbertSchmidt_double_coset_invariant (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (g s s' : Formalism.REAL.UJ (X.B.I.ε v))
    (hs : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat s))
    (hs' : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat s')) :
    hs2 (JvX X u u' v (s * g * s'⁻¹)) = hs2 (JvX X u u' v g) := by
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  haveI := FiniteDimensional.complete ℂ (X.Vloc u' v)
  obtain ⟨A, hA⟩ := wloc_unit X u v s hs
  obtain ⟨B, hB⟩ := wloc_unit X u' v s' hs'
  unfold JvX Formalism.L2.SG.RealObj.Jv
  rw [Formalism.L2.SG.RealObj.InfCut.OO_equiv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) g s s' 1 1 A B hA hB,
    Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_smul, Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_comp_left _ _ (fun x => A.norm_map x),
    Formalism.L2.SG.RealObj.InfCut.hilbert_schmidt_comp_right]
  simp

theorem jvX_meas (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Measurable (fun g => hs2 (JvX X u u' v g)) := by
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  have hF : Continuous (fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) =>
      Formalism.L2.SG.TermOp.rk1 (X.Wloc u v p.2) (X.Wloc u' v (p.1⁻¹ * p.2))) :=
    Formalism.L2.SG.RealObj.RankOneTensors.continuous_rankOneOperator ((X.Wloc_cont u v).comp continuous_snd)
      ((X.Wloc_cont u' v).comp ((continuous_fst.inv).mul continuous_snd))
  have hJ : StronglyMeasurable (fun g => JvX X u u' v g) := by
    have := hF.stronglyMeasurable.integral_prod_right' (ν := Formalism.REAL.muG (X.B.I.ε v))
    unfold JvX Formalism.L2.SG.RealObj.Jv Formalism.L2.SG.TermOp.OO
    simpa [Measure.restrict_univ] using this
  have hc : Continuous (fun A : X.Vloc u' v →L[ℂ] X.Vloc u v => hs2 A) := by
    unfold hs2
    exact continuous_finsetSum _ fun i _ =>
      ((ContinuousLinearMap.apply ℂ (X.Vloc u v) (stdOrthonormalBasis ℂ (X.Vloc u' v) i)).continuous.norm.pow 2)
  exact hc.measurable.comp hJ.measurable

end Loc

def StepSecX : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    ∃ h : (Fin (D.R.rS + 1) → ℂ) → Formalism.REAL.UJ (X.B.I.ε v), Measurable h ∧
      ∀ cv ∈ GoodV (D := D) u u', Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat (h cv)) = Matrix.diagonal cv

theorem locRep_of_sec (hS : StepSecX) {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) :
    ∃ L, LocRep X u u' L := by
  classical
  choose h hm hsec using hS D X u u'
  refine ⟨fun v cv => hs2 (JvX X u u' v (h v cv)),
    ⟨fun v => ⟨(jvX_meas X u u' v).comp (hm v), fun cv => hilbertSchmidt_sq_nonneg _⟩, ?_⟩⟩
  intro c hc v
  have hex : ∃ γ, HasDiag X u u' 1 c γ := ⟨fun w => h w (c w), fun w => hsec w (c w) (hc w)⟩
  have hh : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf; rw [dif_pos hex]; exact hex.choose_spec
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ee, map_zero]
  have hez : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 :=
    fun w a => by
      rw [show X.eR a = X.crd (X.eX a) from rfl, show X.zR w = X.crd (X.zu w) from rfl,
        Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth w a).1, map_zero]
  obtain ⟨s, s', hs, hs', heq⟩ := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.diagDC_pair (X.B.I.ε v) 1 _ _ _ (Tw u) (Tw u')
    hee (hez u) (hez u') (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u) (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hermitian_z_z_eq_neg X v u')
    (c v) (hc v).1 (hc v).2 (h v (c v)) ((hOf X u u' 1 c) v) (hsec v (c v) (hc v)) (hh v)
  show hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = hs2 (JvX X u u' v (h v (c v)))
  rw [heq]
  exact hilbertSchmidt_double_coset_invariant X u u' v _ s s' hs hs'

end Formalism.L2.SG.Pf.Carrier.EnergyPfLoc
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

namespace Formalism.L2.SG.LeadingMinorsNonvanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leading_minor_ne_zero {D : D7} {T T' : ℕ} (hT : 0 < T) (F : LFlag (hS D) D.R.rS (T : D.host.E))
    (F' : LFlag (hS D) D.R.rS (T' : D.host.E)) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hG : Gval F F' ≠ 0) :
    Dr1 F F' ≠ 0 := by
  intro h0
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have h1 := (b_G_pos (p_starConj D) hT F F' hz hz' hG (p_posX D T hT F) τ).1
  rw [b_tauG (p_starConj D) F F' τ, h0, map_zero, norm_zero, Complex.ofReal_re] at h1
  have h2 : (0:ℝ) ≤ (T:ℝ) * T' * ‖τ (Dr F F')‖ ^ 2 := by positivity
  nlinarith

theorem atSomeAll_holds : Formalism.L2.SG.TermTieOf.AtSomeAll := by
  intro D X Y u u' t hG hrel
  obtain ⟨F', ⟨hP, hmk⟩, hR⟩ := hrel
  have hf := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) _ ((Y.rowsOK u).1 t.lam t.mem)
  have hGv : Gval (lf D (X.Fu u)) F' ≠ 0 := by
    have e := Formalism.L2.SG.TermDef.Gt_mk hf.1 ⟨F', hP⟩
    rw [hmk] at e
    exact fun h0 => hG (e.trans h0)
  have hTu := tie_Tu_pos D u
  have hTu' := tie_Tu_pos D u'
  have hDr1 : Dl (lf D (X.Fu u)).fl F'.fl (D.R.rS + 1) ≠ 0 :=
    leading_minor_ne_zero hTu (lf D (X.Fu u)) F' rfl hP.1.2 hGv
  have geo := cell_geom D.host.F D.host.E (hS D) D.R.rS _ _ (lf D (X.Fu u)).fl F'.fl (tie_trace D.sp.cm)
    (tie_aniso D _ hTu (lf D (X.Fu u))) (tie_aniso D _ hTu' F') hR
  obtain ⟨p, hp⟩ := cell_of_matRel cell_inv cell_sign cell_bruhat cell_mono cell_point (le_refl (D.R.rS + 1))
    ((Zhat (lf D (X.Fu u)).fl F'.fl).submatrix (Fin.castLE (le_refl (D.R.rS + 1))) (Fin.castLE (le_refl (D.R.rS + 1))))
    (by rw [← tie_Dl_eq']; exact hDr1) (geo (D.R.rS + 1) le_rfl (Or.inr ⟨rfl, hGv⟩))
  refine ⟨p, F', ⟨hP, hmk⟩, hGv, ?_⟩
  obtain ⟨L, U, hL, hU, hZ⟩ := hp
  refine ⟨L, U, hL, hU, ?_⟩
  rw [← hZ]
  funext a b
  first
  | rfl
  | (simp [ZhatOM, ZhatL, Matrix.submatrix_apply]; rfl)

end Formalism.L2.SG.LeadingMinorsNonvanishing

end
end

