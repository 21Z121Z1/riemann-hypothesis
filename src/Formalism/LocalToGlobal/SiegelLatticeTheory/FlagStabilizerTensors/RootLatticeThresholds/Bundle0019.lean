import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0017

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPlace
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPlace

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def lamA (P : Parts X u u') (a : Fin P.S.G.r) : ℝ := ((P.S.g : ℝ) / (2 * Real.pi)) ^ (2 * (P.S.G.r - a.val))

def phiQ (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (cv : Fin (D.R.rS + 1) → ℂ) : (Fin P.S.G.r → ℂ) × ℂ :=
  (fun a => ((lamA P a : ℝ) : ℂ) * cv ⟨a.val, by have := a.2; omega⟩, cv ⟨D.R.rS, by omega⟩)

def K0 (P : Parts X u u') : ℝ :=
  2 ^ (P.S.G.r + 1) * ∏ a : Fin P.S.G.r, (lamA P a ^ (2 * (Formalism.QuantumDeterminants.Mdim P.S.G.k P.S.G.r a - 1)))⁻¹

def PlaceNorm (P : Parts X u u') (hr : P.S.G.r = D.R.rS)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) : Prop :=
  ∀ v, ∀ cv ∈ GoodV u u', L v cv =
    ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
      (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖ ^ 2

def ChangeVar (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  P.S.G.k = D.R.k →
    (∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u') →
    ∀ v (F : (Fin P.S.G.r → ℂ) × ℂ → ℝ), (∀ q, 0 ≤ F q) →
      ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * F (phiQ P hr cv)) ∂(dcV (D := D)) =
        ENNReal.ofReal (K0 P) * ∫⁻ q, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight P.S.G.k P.S.G.r
          (Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z)
          (Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z') q * F q)

def NormFin (P : Parts X u u') : Prop := ∀ j, Formalism.FourierDecayAlt.B.normSq (P.T j).base (P.f j) ≠ ⊤

def KMatch (P : Parts X u u') : Prop :=
  (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) → Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE → P.S.G.r = D.R.rS →
    P.S.G.k = D.R.k → 0 < P.S.g → 1 ≤ P.S.G.k → K0 P = EnergyConst.Kexp P

end Formalism.L2.SG.Pf.Carrier.EnergyPlace
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PiProd

set_option backward.isDefEq.respectTransparency false in

theorem lintegral_fin_nat_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
        = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi fun i => μ (Fin.succ i))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero]
          simp
      _ = (∫⁻ x, f 0 x ∂(μ 0)) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ (Fin.succ i)) := by
          rw [← ih (fun i => f (Fin.succ i)) (fun i => hf _)]
          exact lintegral_prod_mul (hf 0).aemeasurable
            (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

theorem lintegral_fintype_prod {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod (fun i => f (e i)) (fun i => hf _)

theorem pi_withDensity {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hfin : ∀ i x, f i x ≠ ⊤) :
    Measure.pi (fun i => (μ i).withDensity (f i)) = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  haveI : ∀ i, SigmaFinite ((μ i).withDensity (f i)) := fun i =>
    SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall (hfin i))
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_fintype_prod _ hf]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

end PiProd

section WeilGen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem weil_of_bruhat (μG μS : Measure G) [SigmaFinite μG] [SFinite μS] [μG.IsMulLeftInvariant]
    (B : G → ℝ≥0∞) (hBm : Measurable B) (hinv : μS.map (fun s => s⁻¹) = μS)
    (hb1 : ∀ x, ∫⁻ s, B (s * x) ∂μS = 1) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂(μG.withDensity B) := by
  have hF : Measurable fun p : G × G => f (p.1 * p.2) := hf.comp measurable_mul
  have hg : Measurable fun x => ∫⁻ s, f (s * x) ∂μS := hF.lintegral_prod_left'
  have hBinv : ∀ x, ∫⁻ s, B (s⁻¹ * x) ∂μS = 1 := by
    intro x
    have h1 : ∫⁻ s, B (s * x) ∂(μS.map fun s => s⁻¹) = ∫⁻ s, B (s⁻¹ * x) ∂μS :=
      lintegral_map (hBm.comp (measurable_mul_const x)) measurable_inv
    rw [← h1, hinv, hb1]
  rw [lintegral_withDensity_eq_lintegral_mul _ hBm hg]
  symm
  calc _ = ∫⁻ x, ∫⁻ s, B x * f (s * x) ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply]
        exact (lintegral_const_mul _ (hf.comp (measurable_mul_const x))).symm
    _ = ∫⁻ s, ∫⁻ x, B x * f (s * x) ∂μG ∂μS :=
        lintegral_lintegral_swap
          ((hBm.comp measurable_fst).mul (hf.comp (measurable_snd.mul measurable_fst))).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, B (s⁻¹ * x) * f x ∂μG ∂μS := by
        refine lintegral_congr fun s => ?_
        simpa only [inv_mul_cancel_left] using
          lintegral_mul_left_eq_self (μ := μG) (fun x => B (s⁻¹ * x) * f x) s
    _ = ∫⁻ x, ∫⁻ s, B (s⁻¹ * x) * f x ∂μS ∂μG :=
        lintegral_lintegral_swap
          ((hBm.comp (measurable_fst.inv.mul measurable_snd)).mul (hf.comp measurable_snd)).aemeasurable
    _ = ∫⁻ x, f x ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [show ∫⁻ s, B (s⁻¹ * x) * f x ∂μS = (∫⁻ s, B (s⁻¹ * x) ∂μS) * f x from
          lintegral_mul_const _ (hBm.comp (measurable_inv.mul_const x)), hBinv, one_mul]

end WeilGen

variable {D : D7}

def NV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {g | Formalism.L2.SG.HidaSetting.InN (X.B.I.ε v) (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a))
    (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) (uMat g)}

def StV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  StSet (NV X u v) (NV X u' v) (γ v)

def stCoordV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) (y : Formalism.REAL.UJ (X.B.I.ε v)) : FreeE w → ℂ :=
  fun p => ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1)) *
    Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v)
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR ⟨p.1.1.1, by have := p.2.1; omega⟩))
      (uMat ((γ v)⁻¹ * y * γ v) *ᵥ frm X u' D.host.rdE v p.1.2)

def muStabV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : Point D.host.E (D.R.rS + 1)) : Measure (FreeE w → ℂ) :=
  Measure.pi fun _ => ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) • (volume : Measure ℂ)

theorem stCoord_eq (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ y : X.B.I.Ginf) : stCoord X u' w γ y = fun v => stCoordV X u' w γ v (y v) := rfl

theorem muStab_eq (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : Point D.host.E (D.R.rS + 1)) :
    muStab X w = Measure.pi fun _ => muStabV X w := rfl

def LocPinAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ v, ∃ μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)), IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv ∧
    IsQuotLoc μRv (ν v) ∧ μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w

def LocPin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  LocPinAt X u u' w (νl w)

def LocUni (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w → ∀ v, ∃ μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
    IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv ∧ μRv.map (fun s => s⁻¹) = μRv ∧
    μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w ∧
    ∃ b : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable b ∧ (∀ x, b x ≠ ⊤) ∧ ∀ x, ∫⁻ s, b (s * x) ∂μRv = 1

def GlobProd (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w →
    ∀ μRv : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      (∀ v, IsHaarLoc (StV X u u' (gamW X u u' w) v) (μRv v) ∧
        (μRv v).map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w) →
      μR = Measure.pi μRv

theorem ooQuot_pin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) (hR : StRel X u u')
    (hLU : LocUni X u u') (hGP : GlobProd X u u') :
    ∃ νl, (∀ w, OkPt X u u' w → LocPin X u u' w νl) ∧ Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' νq νl := by
  have hI := stInv_of_rel X u u' hR
  have key : ∀ w : Point D.host.E (D.R.rS + 1),
      ∃ ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)), OkPt X u u' w →
        LocPinAt X u u' w ν ∧ ∀ y : ∀ v, X.Vloc u' v,
          (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
            Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
              (X.tensU u' y) =
          X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
            Jv (ν v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) (y v)) := by
    intro w
    by_cases hw : OkPt X u u' w
    · obtain ⟨μR, hH, hQ, hM⟩ := hN.2 w hw.1
      haveI : SigmaFinite μR := hH.1
      choose μRv hHv hIv hMv b hbm hbt hb1 using hLU w hw μR hH hM
      have hprod : μR = Measure.pi μRv := hGP w hw μR hH hM μRv fun v => ⟨hHv v, hMv v⟩
      haveI : ∀ v, SigmaFinite (μRv v) := fun v => (hHv v).1
      have hσ : ∀ v, SigmaFinite ((Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v)) :=
        fun v => SigmaFinite.withDensity_of_ne_top' (hbt v)
      have hBm : Measurable fun x : X.B.I.Ginf => ∏ v, b v (x v) :=
        Finset.measurable_prod _ fun v _ => (hbm v).comp (measurable_pi_apply v)
      have hb1G : ∀ x : X.B.I.Ginf, ∫⁻ s, (∏ v, b v ((s * x) v)) ∂μR = 1 := by
        intro x
        rw [hprod]
        have := lintegral_fintype_prod (μ := μRv) (fun v t => b v (t * x v))
          (fun v => (hbm v).comp (measurable_mul_const _))
        refine this.trans ?_
        exact Finset.prod_eq_one fun v _ => hb1 v (x v)
      have hinvG : μR.map (fun s => s⁻¹) = μR := by
        haveI : ∀ v, SigmaFinite ((μRv v).map (fun s => s⁻¹)) := fun v => by rw [hIv v]; infer_instance
        rw [hprod]
        have := Measure.pi_map_pi (μ := μRv) (f := fun _ s => s⁻¹) (fun v => measurable_inv.aemeasurable)
        refine this.trans ?_
        congr 1
        funext v
        exact hIv v
      have hp : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR
          (Measure.pi fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v)) := by
        intro f hf
        rw [pi_withDensity _ b hbm hbt]
        exact weil_of_bruhat (Formalism.L2.SG.ProjRows.muInf X.B.I) μR _ hBm hinvG hb1G f hf
      refine ⟨fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v), fun _ => ⟨fun v => ?_, fun y => ?_⟩⟩
      · refine ⟨μRv v, hHv v, fun f hf => ?_, hMv v⟩
        exact weil_of_bruhat (Formalism.REAL.muG (X.B.I.ε v)) (μRv v) (b v) (hbm v) (hIv v) (hb1 v) f hf
      · exact oo_eq_tens X u u' _ μR _ _ hH.2.2.1 _ hBm hb1G _ hσ hQ hp (hI w hw) y
    · exact ⟨fun v => Formalism.REAL.muG (X.B.I.ε v), fun h => absurd h hw⟩
  choose νl hνl using key
  exact ⟨νl, fun w hw => (hνl w hw).1, fun w hw hG y => (hνl w ⟨hw, hG⟩).2 y⟩

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ConstPinOfStd
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.EnergyConst2

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf Formalism.L2.SG.Pf.Carrier.EnergyConst

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

variable (X u u') in

def LemmaMSStd (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : Prop :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ → Formalism.L2.SG.LocVol.IsStdChar ψ → Formalism.L2.SG.LocVol.ProdConv X u u' ψ →
    LemmaMS X u u' ψ

end Formalism.L2.SG.Pf.Carrier.EnergyConst2
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MemPerpMapFlag
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Flag

variable {D : D7} {T : D.host.E} (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)

theorem mapFlag_inv (F0 : FlagG (VS D) D.R.rS T) :
    Formalism.L2.SG.Saturated.mapFlag β⁻¹ (inv_mem hβ) (Formalism.L2.SG.Saturated.mapFlag β hβ F0) = F0 := by
  have key : ∀ x, (β⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (β x) = x := fun x => β.symm_apply_apply x
  cases F0
  simp only [Formalism.L2.SG.Saturated.mapFlag, key]
  all_goals rfl

theorem stabF_conj (F0 : FlagG (VS D) D.R.rS T) {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    β * γ * β⁻¹ ∈ stabF D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) := by
  simp only [stabF] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  have hXa : ∀ j, (Formalism.L2.SG.Saturated.mapFlag β hβ F0).Xa j =
      (F0.Xa j).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    intro j
    first
      | rfl
      | (simp only [FlagG.Xa, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, ← Set.range_comp]; rfl)
      | (simp only [FlagG.Xa, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, Set.image_image]; rfl)
      | simp [FlagG.Xa, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, Set.image_image, ← Set.range_comp]
  have hc : ((β * γ * β⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).comp
      (β : (VS D).V →ₗ[D.host.E] (VS D).V) =
      (β : (VS D).V →ₗ[D.host.E] (VS D).V).comp (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    ext x
    show β (γ (β.symm (β x))) = β (γ x)
    rw [β.symm_apply_apply]
  refine ⟨mul_mem (mul_mem hβ h1) (inv_mem hβ), fun j => ?_, ?_⟩
  · rw [hXa j, ← Submodule.map_comp, hc, Submodule.map_comp, h2 j]
  · show β (γ (β.symm (β F0.z))) = β F0.z
    rw [β.symm_apply_apply, h3]

theorem stabF_conj_inv (F0 : FlagG (VS D) D.R.rS T) {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hγ : γ ∈ stabF D (Formalism.L2.SG.Saturated.mapFlag β hβ F0)) : β⁻¹ * γ * β ∈ stabF D F0 := by
  have h := stabF_conj β⁻¹ (inv_mem hβ) (Formalism.L2.SG.Saturated.mapFlag β hβ F0) hγ
  rwa [mapFlag_inv, inv_inv] at h

end Flag

theorem RowRepsIso_holds (D : D7) : Formalism.L2.SG.TermTieOf.RowRepsIso D := by
  have hL := LatIso_holds D
  intro β hβ T F0 what₂ hR
  obtain ⟨hrow, huniq⟩ := hR
  refine ⟨?_, ?_⟩
  · intro Λ hΛ
    obtain ⟨Λ0, h0, rfl⟩ := Finset.mem_image.1 hΛ
    exact Formalism.L2.SG.TermTieOf.rowLat_map hL β hβ F0 Λ0 (hrow Λ0 h0)
  · intro Λ hΛ
    have h0 : IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap β⁻¹ Λ) := by
      have h := Formalism.L2.SG.TermTieOf.rowLat_map hL β⁻¹ (inv_mem hβ) (Formalism.L2.SG.Saturated.mapFlag β hβ F0) Λ hΛ
      rw [mapFlag_inv] at h
      exact h
    obtain ⟨M, ⟨hM, γ, hγ, hγM⟩, hU⟩ := huniq _ h0
    refine ⟨Formalism.HermitianLatticesTheory.gmap β M, ⟨Finset.mem_image_of_mem _ hM, β * γ * β⁻¹, stabF_conj β hβ F0 hγ, ?_⟩, ?_⟩
    · rw [gmap_mul, gmap_mul, gmap_inv_gmap, hγM, gmap_gmap_inv]
    · rintro N ⟨hN, γ', hγ', hγN⟩
      obtain ⟨M', hM', rfl⟩ := Finset.mem_image.1 hN
      have hM'M : M' = M := by
        refine hU M' ⟨hM', β⁻¹ * γ' * β, stabF_conj_inv β hβ F0 hγ', ?_⟩
        rw [gmap_mul, gmap_mul, hγN]
      rw [hM'M]

section Wb

variable {D : D7} {T : D.host.E} (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
  (F0 : FlagG (VS D) D.R.rS T)

theorem perp_mapFlag :
    perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X =
      (perpS (VS D) F0.X).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
  have hb : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y := by
    intro x y
    first
      | exact hβ x y
      | exact LinearMap.congr_fun₂ hβ x y
      | exact Formalism.HermitianLatticesTheory.isom_apply hβ x y
      | exact Formalism.L2.SG.Saturated.isom_apply hβ x y
      | exact isom_apply hβ x y
  have hX : (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X = F0.X.map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    first
      | rfl
      | (simp only [FlagG.X, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, ← Set.range_comp]; rfl)
      | (simp only [FlagG.X, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, Set.image_union,
          Set.image_singleton, ← Set.range_comp]; rfl)
      | simp [FlagG.X, Formalism.L2.SG.Saturated.mapFlag, Submodule.map_span, ← Set.range_comp, Set.image_union]
  ext y
  rw [hX, Submodule.mem_map_equiv]
  simp only [perpS, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    have h1 := h (β x) (Submodule.mem_map_of_mem hx)
    rwa [← β.apply_symm_apply y, hb] at h1
  · intro h x hx
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
    have h2 := hb x' (β.symm y)
    rw [β.apply_symm_apply] at h2
    exact h2.trans (h x' hx')

theorem mem_perp_mapFlag {y : (VS D).V} :
    y ∈ perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X ↔ β.symm y ∈ perpS (VS D) F0.X := by
  rw [perp_mapFlag β hβ F0, Submodule.mem_map_equiv]

def perpEq : ↥(perpS (VS D) F0.X) ≃ₗ[D.host.E] ↥(perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X) :=
  LinearEquiv.ofSubmodules β _ _ (perp_mapFlag β hβ F0).symm

theorem perpEq_map :
    Submodule.map (perpEq β hβ F0 : ↥(perpS (VS D) F0.X) →ₗ[D.host.E] ↥(perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X))
      (F0.X.comap (perpS (VS D) F0.X).subtype) =
      (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X.comap
        (perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X).subtype := by
  ext ⟨y, hy⟩
  rw [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hxX, hfx⟩
    rw [Submodule.mem_comap, Submodule.subtype_apply] at hxX
    show y ∈ _
    rw [Formalism.L2.SG.Pf.X_mapFlag β hβ F0, Submodule.mem_map]
    exact ⟨x.1, hxX, congrArg Subtype.val hfx⟩
  · intro hyX
    have hyX' : y ∈ F0.X.map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [← Formalism.L2.SG.Pf.X_mapFlag β hβ F0]; exact hyX
    obtain ⟨x, hxX, rfl⟩ := (Submodule.mem_map).1 hyX'
    have hx0 : x ∈ perpS (VS D) F0.X := by
      have h := (mem_perp_mapFlag β hβ F0).1 hy
      have e : β.symm ((β : (VS D).V →ₗ[D.host.E] (VS D).V) x) = x := β.symm_apply_apply x
      rwa [e] at h
    exact ⟨⟨x, hx0⟩, hxX, Subtype.ext rfl⟩

def wbEquiv : WbQ D F0 ≃ WbQ D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) :=
  (Submodule.Quotient.equiv _ _ (perpEq β hβ F0) (perpEq_map β hβ F0)).toEquiv

theorem wbEquiv_mk (x : ↥(perpS (VS D) F0.X)) :
    wbEquiv β hβ F0 (Submodule.Quotient.mk x) = Submodule.Quotient.mk (perpEq β hβ F0 x) := rfl

theorem autLz_fwd {Λ : Submodule (𝓞 D.host.E) (VS D).V} {φ : WbQ D F0 → WbQ D F0} (hφ : φ ∈ autLz D F0 Λ) :
    (wbEquiv β hβ F0) ∘ φ ∘ (wbEquiv β hβ F0).symm ∈
      autLz D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) := by
  obtain ⟨γ, hγ, hΛ, hφ⟩ := hφ
  refine ⟨β * γ * β⁻¹, stabF_conj β hβ F0 hγ, ?_, ?_⟩
  · rw [gmap_mul, gmap_mul, gmap_inv_gmap, hΛ]
  · intro x hx
    have hy0 : β.symm x.1 ∈ perpS (VS D) F0.X := (mem_perp_mapFlag β hβ F0).1 x.2
    have hy1 : γ (β.symm x.1) ∈ perpS (VS D) F0.X := by
      have h := (mem_perp_mapFlag β hβ F0).1 hx
      have key : β.symm ((β * γ * β⁻¹) x.1) = γ (β.symm x.1) := by
        show β.symm (β (γ (β.symm x.1))) = _
        exact β.symm_apply_apply _
      rwa [key] at h
    have e1 : (wbEquiv β hβ F0).symm (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨β.symm x.1, hy0⟩ := by
      rw [Equiv.symm_apply_eq, wbEquiv_mk]
      congr 1
      exact Subtype.ext (β.apply_symm_apply x.1).symm
    simp only [Function.comp_apply]
    rw [e1, hφ ⟨β.symm x.1, hy0⟩ hy1, wbEquiv_mk]
    congr 1

theorem autLz_bwd {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {ψ : WbQ D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) → WbQ D (Formalism.L2.SG.Saturated.mapFlag β hβ F0)}
    (hψ : ψ ∈ autLz D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ)) :
    (wbEquiv β hβ F0).symm ∘ ψ ∘ (wbEquiv β hβ F0) ∈ autLz D F0 Λ := by
  obtain ⟨γ, hγ, hΛ, hψ⟩ := hψ
  refine ⟨β⁻¹ * γ * β, stabF_conj_inv β hβ F0 hγ, ?_, ?_⟩
  · rw [gmap_mul, gmap_mul, hΛ, gmap_inv_gmap]
  · intro x hx
    have hx1 : γ (β x.1) ∈ perpS (VS D) (Formalism.L2.SG.Saturated.mapFlag β hβ F0).X := by
      rw [mem_perp_mapFlag β hβ F0]
      exact hx
    simp only [Function.comp_apply]
    rw [wbEquiv_mk, Equiv.symm_apply_eq, hψ (perpEq β hβ F0 x) hx1, wbEquiv_mk]
    congr 1
    exact Subtype.ext (show γ (β x.1) = β (β.symm (γ (β x.1))) from (β.apply_symm_apply _).symm)

def autEquiv (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    autLz D F0 Λ ≃ autLz D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) where
  toFun φ := ⟨_, autLz_fwd β hβ F0 φ.2⟩
  invFun ψ := ⟨_, autLz_bwd β hβ F0 ψ.2⟩
  left_inv φ := Subtype.ext (funext fun x => by simp)
  right_inv ψ := Subtype.ext (funext fun x => by simp)

end Wb

theorem WRowIso_holds (D : D7) : Formalism.L2.SG.TermTieOf.WRowIso D := by
  intro β hβ T F0 Λ
  simp only [Formalism.MainNotions.S.wRow]
  rw [Nat.card_congr (autEquiv β hβ F0 Λ).symm]

end Formalism.L2.SG.Pf.WittFlags
end
end

