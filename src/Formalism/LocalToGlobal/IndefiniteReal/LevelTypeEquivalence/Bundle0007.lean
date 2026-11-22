import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterEqOfRange

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqAct
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Lev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem levFn_flag_one : Formalism.L2.DIV.levFn β (flagL L) 1 = 1 := by
  have h1 : (1 : GL (Fin V.rank) (EAf D)) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := Subgroup.one_mem _
  exact (Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L)).map_one

theorem levFn_conj {x y : GL (Fin V.rank) (EAf D)} (hx : x ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L)
    (hy : y ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) :
    Formalism.L2.DIV.levFn β (flagL L) (x⁻¹ * y * x) = Formalism.L2.DIV.levFn β (flagL L) y := by
  have hxi : x⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.inv_mem _ hx
  have hxy : x⁻¹ * y ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.mul_mem _ hxi hy
  rw [levFn_flag_mul hxy hx, levFn_flag_mul hxi hy]
  have e : Formalism.L2.DIV.levFn β (flagL L) x⁻¹ * Formalism.L2.DIV.levFn β (flagL L) x = 1 := by
    rw [← levFn_flag_mul hxi hx, inv_mul_cancel, levFn_flag_one]
  calc Formalism.L2.DIV.levFn β (flagL L) x⁻¹ * Formalism.L2.DIV.levFn β (flagL L) y * Formalism.L2.DIV.levFn β (flagL L) x
      = Formalism.L2.DIV.levFn β (flagL L) y * (Formalism.L2.DIV.levFn β (flagL L) x⁻¹ * Formalism.L2.DIV.levFn β (flagL L) x) := by
        rw [mul_comm (Formalism.L2.DIV.levFn β (flagL L) x⁻¹), mul_assoc]
    _ = Formalism.L2.DIV.levFn β (flagL L) y := by rw [e, mul_one]

theorem mem_levG_flag1 {k : GA D V} :
    k ∈ levG V β (flag1L L) ↔ k ∈ GfC V ∧ finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L ∧
      Formalism.L2.DIV.rTup β L (finE V k) = 1 := by
  show (k ∈ GfC V ∧ (finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L ∧
      Formalism.L2.DIV.rTup β L (finE V k) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r)))) ↔ _
  rw [Subgroup.mem_bot]

theorem levChi_flag1 (k : GA D V) : levChi V β (flag1L L) k = levChi V β (flagL L) k := by
  unfold levChi; rw [levFn_flag1]

theorem hasType_rTrc {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {κ : GA D V} (hκ : κ ∈ GfC V)
    (hκ' : finE V κ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) (c : ℂ) :
    HasType V β (flag1L L) (fun h => c * F (h * κ)) := by
  intro k hk h
  obtain ⟨hk1, hk2, hk3⟩ := mem_levG_flag1.1 hk
  have hki : (finE V κ)⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.inv_mem _ hκ'
  have hm1 : (finE V κ)⁻¹ * finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.mul_mem _ hki hk2
  have hk' : κ⁻¹ * k * κ ∈ levG V β (flag1L L) := by
    refine mem_levG_flag1.2 ⟨?_, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ) hk1) hκ
    · rw [map_mul, map_mul, map_inv]; exact Subgroup.mul_mem _ hm1 hκ'
    · rw [map_mul, map_mul, map_inv, Formalism.L2.DIV.rTup_mul hm1 hκ', Formalism.L2.DIV.rTup_mul hki hk2,
        Formalism.L2.DIV.rTup_inv hκ', hk3, mul_one, inv_mul_cancel]
  have e1 := hF _ hk' (h * κ)
  rw [show h * κ * (κ⁻¹ * k * κ) = h * k * κ by group] at e1
  have e2 : levChi V β (flag1L L) (κ⁻¹ * k * κ) = levChi V β (flag1L L) k := by
    rw [levChi_flag1, levChi_flag1]
    unfold levChi
    rw [map_mul, map_mul, map_inv, levFn_conj hκ' hk2]
  show c * F (h * k * κ) = levChi V β (flag1L L) k * (c * F (h * κ))
  rw [e1, e2]; ring

theorem level_action_eq_lift {g0 : Formalism.L2.DIV.G0 L.Pg L.r} {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {κ : GA D V}
    (hκ : IsLevelLift V β L g0 κ) : actG0 V β L g0 F = fun h => (levChi V β (flagL L) κ)⁻¹ * F (h * κ) := by
  funext h
  exact level_action_spec hF ⟨κ, hκ⟩ κ hκ h

theorem has_type_of_level_action (hL : LiftsExist V β L) (g0 : Formalism.L2.DIV.G0 L.Pg L.r) {F : GA D V → ℂ}
    (hF : HasType V β (flag1L L) F) : HasType V β (flag1L L) (actG0 V β L g0 F) := by
  obtain ⟨κ, hκ⟩ := hL g0
  rw [level_action_eq_lift hF hκ]
  exact hasType_rTrc hF hκ.1 hκ.2.1 _

theorem levelGroupAction_mul_of_lifts (hL : LiftsExist V β L) (g1 g2 : Formalism.L2.DIV.G0 L.Pg L.r) {F : GA D V → ℂ}
    (hF : HasType V β (flag1L L) F) : actG0 V β L g1 (actG0 V β L g2 F) = actG0 V β L (g1 * g2) F := by
  obtain ⟨κ1, hκ1⟩ := hL g1
  obtain ⟨κ2, hκ2⟩ := hL g2
  have h12 : IsLevelLift V β L (g1 * g2) (κ1 * κ2) := by
    refine ⟨Subgroup.mul_mem _ hκ1.1 hκ2.1, ?_, ?_⟩
    · rw [map_mul]; exact Subgroup.mul_mem _ hκ1.2.1 hκ2.2.1
    · rw [map_mul, Formalism.L2.DIV.rTup_mul hκ1.2.1 hκ2.2.1, hκ1.2.2, hκ2.2.2]
  have hF2 := has_type_of_level_action hL g2 hF
  rw [level_action_eq_lift hF2 hκ1, level_action_eq_lift hF h12, level_action_eq_lift hF hκ2]
  funext h
  have e : levChi V β (flagL L) (κ1 * κ2) = levChi V β (flagL L) κ1 * levChi V β (flagL L) κ2 := by
    unfold levChi; rw [map_mul, levFn_flag_mul hκ1.2.1 hκ2.2.1, Units.val_mul]
  have ha := levChi_ne_zero (β := β) (flagL L) κ1
  have hb := levChi_ne_zero (β := β) (flagL L) κ2
  simp only [e, mul_assoc]
  field_simp

end Formalism.IndefR.Eqv.Act

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.PeterssonNormOfUpLift
section
noncomputable section

open MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

def RightInv : Prop :=
  ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (Γ : Subgroup H) [Countable Γ]
    (ν : Measure H) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (𝓕 : Set H),
    IsFundamentalDomain Γ 𝓕 ν → ∀ ψ : H → ℂ, (∀ γ ∈ Γ, ∀ h, ψ (γ * h) = ψ h) → ∀ k : H,
      (IntegrableOn (fun h => ψ (h * k)) 𝓕 ν ↔ IntegrableOn ψ 𝓕 ν) ∧
        ∫ h in 𝓕, ψ (h * k) ∂ν = ∫ h in 𝓕, ψ h ∂ν

section GA

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def UnimodGA (V : HSp D) : Prop :=
  ∀ μ : Measure (GA D V), μ.IsHaarMeasure → μ.IsMulRightInvariant

def RightInvGA (V : HSp D) : Prop :=
  MeasurableMul (GA D V) → Countable (GQ V) → UnimodGA V →
    ∀ (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
      Lev.IsMeasFD V K μ 𝓕 → ∀ ψ : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ h, ψ (γ * h) = ψ h) → ∀ k : GA D V,
        (IntegrableOn (fun h => ψ (h * k)) 𝓕 μ ↔ IntegrableOn ψ 𝓕 μ) ∧
          ∫ h in 𝓕, ψ (h * k) ∂μ = ∫ h in 𝓕, ψ h ∂μ

end GA

def IoExistsOf : Prop :=
  ∀ (G H S Sinf Ds Dt : Type) [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds]
    [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (pt : Sinf → S)
    (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))) (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))),
    (∀ F : CCs, ∀ φ v g, IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h) 𝓕 ν) →
    (∀ F : CCs, ∃ u : CCt, ∀ φ v g,
      (u : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) g = Lift.liftInt ν 𝓕 th (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v) g) →
    (∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) = 0) → u = 0) →
    Lift.IoExists ν 𝓕 th pt T CCs CCt

section Mult

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def IoUniqueAt : Prop :=
  ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : Mult.DSModel V S)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Kf : ∀ τ, Submodule ℂ (M.sm τ)) (Sinf Ds : Type) [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds]
    [Module ℂ Ds] (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] (⨂[ℂ] τ, M.sm τ)),
    (∀ τ (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (∀ w ∈ Kf τ, ℓ (w : M.H τ) = 0) →
      ∀ w : M.sm τ, ℓ (w : M.H τ) = 0) →
    (∀ v : ∀ τ, M.sm τ, (∀ τ, v τ ∈ Kf τ) →
      PiTensorProduct.tprod ℂ v ∈ Submodule.span ℂ {x | ∃ φ w, T φ w = x}) →
    ∀ u ∈ Mult.MultT θ M J χ, (∀ φ w, u (T φ w) = 0) → u = 0

def IoUniqueIo : Prop :=
  ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : Mult.DSModel V S)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Kf : ∀ τ, Submodule ℂ (M.sm τ)) (Sinf Ds : Type) [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds]
    [Module ℂ Ds] (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] (⨂[ℂ] τ, M.sm τ)) (H S' : Type) [MeasurableSpace H] (ν : Measure H)
    (𝓕 : Set H) (th : GA D V → H → S' → ℂ) (pt : Sinf → S') (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (io io' : CCs →ₗ[ℂ] Mult.MultT θ M J χ),
    (∀ τ (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (∀ w ∈ Kf τ, ℓ (w : M.H τ) = 0) →
      ∀ w : M.sm τ, ℓ (w : M.H τ) = 0) →
    (∀ v : ∀ τ, M.sm τ, (∀ τ, v τ ∈ Kf τ) →
      PiTensorProduct.tprod ℂ v ∈ Submodule.span ℂ {x | ∃ φ w, T φ w = x}) →
    Lift.IsIo ν 𝓕 th pt T CCs (Mult.MultT θ M J χ) io → Lift.IsIo ν 𝓕 th pt T CCs (Mult.MultT θ M J χ) io' →
      io = io'

end Mult

def rtr {H Ds : Type*} [Mul H] [AddCommGroup Ds] [Module ℂ Ds] (b : H) (F : Ds →ₗ[ℂ] (H → ℂ)) :
    Ds →ₗ[ℂ] (H → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun h => h * b) ∘ₗ F

def LiftEquiv : Prop :=
  ∀ (G H S Sinf Ds Dt : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H]
    [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt]
    (Γ : Subgroup H) [Countable Γ] (ν : Measure H) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (𝓕 : Set H)
    (th : G → H → S → ℂ) (pt : Sinf → S) (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt)
    (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))) (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (io : CCs →ₗ[ℂ] CCt)
    (ι κ : Type) [Fintype ι] [Fintype κ] (b : ι → H) (c : ι → ℂ) (a : κ → G) (d : κ → ℂ),
    IsFundamentalDomain Γ 𝓕 ν →
    (∀ F : CCs, ∀ v, ∀ γ ∈ Γ, ∀ h, (F : Ds →ₗ[ℂ] (H → ℂ)) v (γ * h) = (F : Ds →ₗ[ℂ] (H → ℂ)) v h) →
    (∀ g φ, ∀ γ ∈ Γ, ∀ h, th g (γ * h) (pt φ) = th g h (pt φ)) →
    (∀ g h φ, ∑ i, c i * th g (h * (b i)⁻¹) (pt φ) = ∑ k, d k * th (g * a k) h (pt φ)) →
    (∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) = 0) → u = 0) →
    Lift.IsIo ν 𝓕 th pt T CCs CCt io →
    ∀ F : CCs, (∀ i φ v g, IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * b i)) 𝓕 ν) →
      ∀ F' : CCs, (F' : Ds →ₗ[ℂ] (H → ℂ)) = ∑ i, c i • rtr (b i) (F : Ds →ₗ[ℂ] (H → ℂ)) →
        ∀ u : CCt, (u : Dt →ₗ[ℂ] (G → ℂ)) = ∑ k, d k • rtr (a k) ((io F : CCt) : Dt →ₗ[ℂ] (G → ℂ)) →
          io F' = u

def PeterssonLiftIdentity : Prop :=
  ∀ (G H S Sinf Ds Dt : Type) [MeasurableSpace G] [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf]
    [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) [SFinite ν] (𝓕 : Set H)
    (νG : Measure G) [SFinite νG] (𝓕G : Set G) (th : G → H → S → ℂ) (pt : Sinf → S) (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt)
    (Tp : Sinf →ₗ⋆[ℂ] Dt →ₗ[ℂ] Ds) (ipDs : Ds →ₗ[ℂ] Ds →ₗ⋆[ℂ] ℂ) (ipDt : Dt →ₗ[ℂ] Dt →ₗ⋆[ℂ] ℂ)
    (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))) (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ)))
    (ipS : CCs →ₗ[ℂ] CCs →ₗ⋆[ℂ] ℂ) (ipT : CCt →ₗ[ℂ] CCt →ₗ⋆[ℂ] ℂ) (io : CCs →ₗ[ℂ] CCt) (up : CCt →ₗ[ℂ] CCs),
    Lift.AdjointLiftPeterssonIdentity ν 𝓕 νG 𝓕G th pt T Tp ipDs ipDt CCs CCt ipS ipT io up

def PeterssonNormOfUpLift : Prop :=
  ∀ (G H S Sinf Ds Dt : Type) [MeasurableSpace G] [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf]
    [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) (𝓕 : Set H)
    (νG : Measure G) (𝓕G : Set G) (th : G → H → S → ℂ) (pt : Sinf → S) (Tp : Sinf →ₗ⋆[ℂ] Dt →ₗ[ℂ] Ds)
    (ipDs : Ds →ₗ[ℂ] Ds →ₗ⋆[ℂ] ℂ) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))) (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ)))
    (ipS : CCs →ₗ[ℂ] CCs →ₗ⋆[ℂ] ℂ) (up : CCt →ₗ[ℂ] CCs),
    Lift.IsSchur ν 𝓕 ipDs CCs ipS → Lift.IsIoUp νG 𝓕G th pt Tp CCs CCt up →
    ∀ (u : CCt) φ v,
      Lift.pet ν 𝓕 (fun h => ∫ g in 𝓕G, starRingEnd ℂ (th g h (pt φ)) * (u : Dt →ₗ[ℂ] (G → ℂ)) v g ∂νG)
          (fun h => ∫ g in 𝓕G, starRingEnd ℂ (th g h (pt φ)) * (u : Dt →ₗ[ℂ] (G → ℂ)) v g ∂νG) =
        ipS (up u) (up u) * ipDs (Tp φ v) (Tp φ v)

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobDer
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem mlin_norm_le {m : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin m => (Fin k → ℝ)) ℂ) :
    ‖M‖ ≤ ∑ l : Fin m → Fin k, ‖M (fun i => ev (l i))‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = fun i => ∑ j, v i j • ev j := by
    funext i
    ext j'
    simp [ev, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv, M.map_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [M.map_smul_univ, norm_smul, norm_prod, mul_comm]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_) (norm_nonneg _)
  exact norm_le_pi_norm (v i) (r i)

def Gf (ψ : AddChar (AF D.host.F) ℂ) (L : (Fin k → ℝ) →+ WO S T) (f : WO S T → ℂ) (x : WO S T) :
    (Fin k → ℝ) → ℂ := fun t => heisO ψ S T (L t) f x

def Ff (L : (Fin k → ℝ) →+ WO S T) (f : WO S T → ℂ) (x : WO S T) : (Fin k → ℝ) → ℂ := fun t => f (x + L t)

def ellAdd (Λ : Ainf D.host.F →+ ℂ) (L : (Fin k → ℝ) →+ WO S T) (x : WO S T) : (Fin k → ℝ) →+ ℂ :=
  AddMonoidHom.mk' (fun t => Λ (symplOH S T x (L t)).1) (fun t t' => by
    simp only [map_add, symplOH_add_right]
    exact Λ.map_add _ _)

theorem continuous_ellAdd (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T)
    (hL : Continuous L) (x : WO S T) : Continuous (ellAdd Λ L x) := by
  have hs : Continuous fun t => symplOH S T x (L t) := (continuous_symplOH_right x).comp hL
  have h1 : Continuous fun t => Λ (symplOH S T x (L t)).1 := hΛ.comp (continuous_fst.comp hs)
  exact h1

def ellx (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T) (hL : Continuous L)
    (x : WO S T) : (Fin k → ℝ) →L[ℝ] ℂ :=
  AddMonoidHom.toRealLinearMap (ellAdd Λ L x) (continuous_ellAdd Λ hΛ L hL x)

theorem ellx_apply (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T) (hL : Continuous L)
    (x : WO S T) (t : Fin k → ℝ) : ellx Λ hΛ L hL x t = Λ (symplOH S T x (L t)).1 := rfl

section Bound

variable {ψ : AddChar (AF D.host.F) ℂ} {Λ : Ainf D.host.F →+ ℂ} (hΛ : Continuous Λ)
  (hψΛ : ∀ z : AF D.host.F, z.2 = 0 → ψ z = Complex.exp (Λ z.1))
  {L : (Fin k → ℝ) →+ WO S T} (hL : IsRealFrame L)

include hΛ hψΛ hL in
theorem Gf_eq (f : WO S T → ℂ) (x : WO S T) :
    Gf ψ L f x = fun t => Complex.exp (ellx Λ hΛ L hL.1 x t) * Ff L f x t := by
  funext t
  have hr : eInf D • L t = L t := (wo_real_iff (L t)).mp (hL.2.1 t)
  simp only [Gf, Ff, heisO, ellx_apply]
  rw [hψΛ _ (symplOH_snd x (L t) hr)]

include hΛ hψΛ hL in
theorem Gf_smooth {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : WO S T) : ContDiff ℝ ∞ (Gf ψ L f x) := by
  rw [Gf_eq hΛ hψΛ hL]
  exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp (ellx Λ hΛ L hL.1 x).contDiff).mul
    (hf.smooth k L hL.1 hL.2.1 x)

end Bound

end Formalism.IndefR.Eqv

end
end

