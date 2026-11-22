import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIxOfMemEigAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

theorem exists_ix_of_mem_eigAt : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m), A3.fam3.Ok3 s → ∀ (x : (A3.rowI A3.A.μ0).OpIx → K) (f : (A3.A.fam.R A3.A.μ0).S.Forms), f ≠ 0 → f ∈ (A3.A.fam.R A3.A.μ0).ZHg A3.A.X → f ∈ Formalism.L2.Col.eigAt (A3.rowI A3.A.μ0).opAll x → ∃ p : A3.fam3.base3.Ix, (A3.rowI A3.A.μ0).HasRes3 p.1 x := by
  classical
  intro K _ _ _ G _ _ Pl0 I0 Ty T m s A3 h x f hf0 hfZ hfx
  have hB : (A3.A.fam.R A3.A.μ0).Ok s := h.ok2.what₂ A3.A.μ0
  have hD : (A3.rowI A3.A.μ0).Ok3 := h.what₂ A3.A.μ0
  have hs := (A3.rowI A3.A.μ0).splitOver_opAll hB hD

  have hfZH : f ∈ Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll fun y => Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i)) :=
    le_eigSum_elim (A3.A.fam.R A3.A.μ0).op (A3.rowI A3.A.μ0).opI hD.comm hs _ (by exact hfZ.1)
  have hHB : Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => x (Sum.inl i)) := by
    by_contra hn
    have hf2 : f ∈ Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll fun y => ¬ Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i)) :=
      Formalism.L2.Col.eigAt_le_eigSum (C := fun y => ¬ Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i))) hn hfx
    exact hf0 (Submodule.disjoint_def.1 (Formalism.L2.Col.disjoint_eigSum hD.comm fun y h1 h2 => h2 h1) f hfZH hf2)
  choose c hc using hHB
  let Sg : Pl0 → K[X] := fun P0 => if hP : ∃ P, (A3.A.fam.R A3.A.μ0).pl P = P0 then c hP.choose else 1
  have hSg : ∀ P, Sg ((A3.A.fam.R A3.A.μ0).pl P) = c P := by
    intro P
    have hP : ∃ P', (A3.A.fam.R A3.A.μ0).pl P' = (A3.A.fam.R A3.A.μ0).pl P := ⟨P, rfl⟩
    simp only [Sg, dif_pos hP]
    rw [hB.pl_inj hP.choose_spec]
  let e : I0 × Ty → K := fun k0 => if hP : ∃ P, (A3.rowI A3.A.μ0).plI P = k0.1 then x (Sum.inr (hP.choose, k0.2)) else 0
  have he : ∀ (P : (A3.rowI A3.A.μ0).PlI) (y : Ty), e ((A3.rowI A3.A.μ0).plI P, y) = x (Sum.inr (P, y)) := by
    intro P y
    have hP : ∃ P', (A3.rowI A3.A.μ0).plI P' = (A3.rowI A3.A.μ0).plI P := ⟨P, rfl⟩
    simp only [e, dif_pos hP]
    rw [hD.plI_inj hP.choose_spec]
  have hres : (A3.rowI A3.A.μ0).HasRes3 (Sg, e) x := by
    refine ⟨fun P => ?_, fun k => (he k.1 k.2).symm⟩
    show _ = Sg ((A3.A.fam.R A3.A.μ0).pl P) * (A3.A.fam.R A3.A.μ0).blockProd P
    rw [hSg P, mul_comm]
    exact hc P

  set a0 := goodAt A3.A.fam.X (⊥ : Subgroup G) 1 with ha0
  have hidem : a0 * a0 = a0 :=
    (good_at_spec K A3.A.fam.v0 h.ok2.conj G A3.A.fam.X h.ok2.irr (⊥ : Subgroup G) 1).idem
  have hfix : (A3.A.fam.R A3.A.μ0).S.gaOp (A3.A.fam.R A3.A.μ0).r a0 f = f := by
    obtain ⟨g, hg⟩ := LinearMap.mem_range.1 hfZ.2
    have hid' : a0 * goodAt A3.A.X (⊥ : Subgroup G) 1 = goodAt A3.A.X (⊥ : Subgroup G) 1 := hidem
    rw [← hg, ← BlockDat.gaOp_mul, hid']
  obtain ⟨u0, hu0⟩ := (A3.A.fam.R A3.A.μ0).exists_vE_of_fix (Lvl.full A3.A.fam.X) hfix
  have hmem : (Sg, e) ∈ (A3.rowI A3.A.μ0).ixFin3 A3.A.fam.X := by
    rw [(A3.rowI A3.A.μ0).mem_ixFin3 hD.comm]
    refine ⟨fun P0 hP0 => ?_, fun P0 hP0 y => ?_, ?_⟩
    · have hP : ¬ ∃ P, (A3.A.fam.R A3.A.μ0).pl P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
      show Sg P0 = 1
      simp only [Sg, dif_neg hP]
    · have hP : ¬ ∃ P, (A3.rowI A3.A.μ0).plI P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
      show e (P0, y) = 0
      simp only [e, dif_neg hP]
    · intro hbot
      have hu0mem : u0 ∈ (A3.A.fam.R A3.A.μ0).inV0 (Lvl.full A3.A.fam.X) ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum (Sg, e)) := by
        rw [BlockDat.mem_goodPart_iff, hu0]
        exact Formalism.L2.Col.eigAt_le_eigSum (C := (A3.rowI A3.A.μ0).HasRes3 (Sg, e)) hres hfx
      rw [hbot, Submodule.mem_bot] at hu0mem
      apply hf0
      rw [← hu0, hu0mem, Matrix.mulVec_zero, map_zero]
  exact ⟨⟨(Sg, e), hmem⟩, hres⟩

end GlobalTheory.Div
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Generic

variable {B Hf W : Type} [Group B] [Group Hf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : B →* Hf) (Γ : Subgroup B)
  (ρ : B →* Module.End ℂ W) {J : Subgroup Hf} {χ : J →* ℂˣ}

theorem rho_mul (a b : B) (w : W) : ρ (a * b) w = ρ a (ρ b w) := by rw [map_mul]; rfl

theorem rho_rho_inv (a : B) (w : W) : ρ a (ρ a⁻¹ w) = w := by rw [← rho_mul, mul_inv_cancel, map_one]; rfl

theorem mem_adForms (s : Hf → B) (hs : ∀ u, π (s u) = u) (hρ : ∀ u, ρ (s u) = 1) (Ψ : B → W)
    (h : ∀ γ ∈ Γ, ∀ k (hk : π k ∈ J), ∀ x, Ψ (γ * x * k) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ k⁻¹ (Ψ x)) :
    (fun u => Ψ (s u)) ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ := by
  intro γ u k
  have e : π (((γ : B) * s u)⁻¹ * s (π γ * u * k)) = k := by
    rw [map_mul, map_inv, map_mul, hs, hs, inv_mul_cancel_left]
  have h1 := h γ γ.2 _ (e ▸ k.2) (s u)
  rw [mul_inv_cancel_left] at h1
  have h2 : ∀ u, ρ (s u)⁻¹ = 1 := fun u => by
    have := map_mul ρ (s u)⁻¹ (s u)
    rwa [inv_mul_cancel, map_one, hρ, mul_one, eq_comm] at this
  refine h1.trans ?_
  have h3 : ρ (((γ : B) * s u)⁻¹ * s (π γ * u * k))⁻¹ = ρ γ := by
    rw [_root_.mul_inv_rev, inv_inv, map_mul, map_mul, h2, hρ, one_mul, mul_one]
  rw [h3]
  congr 3
  exact Subtype.ext e

theorem form_law {f : Hf → W} (hf : f ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) {γ : B} (hγ : γ ∈ Γ) (k : B)
    (hk : π k ∈ J) (x : B) :
    ρ (γ * x * k)⁻¹ (f (π (γ * x * k))) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ k⁻¹ (ρ x⁻¹ (f (π x))) := by
  have h : f (π γ * π x * π k) = ((χ ⟨π k, hk⟩ : ℂˣ) : ℂ) • ρ γ (f (π x)) := hf ⟨γ, hγ⟩ (π x) ⟨π k, hk⟩
  rw [map_mul π, map_mul π, h, map_smul, ← rho_mul, ← rho_mul]
  congr 3
  group

theorem vec_law (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) {a b : W} {z : ℂ} (hz : ‖z‖ = 1) (k : B)
    (h : ∀ w, inner ℂ a w = z⁻¹ * inner ℂ b (ρ k w)) : a = z • ρ k⁻¹ b := by
  refine ext_inner_right ℂ fun w => ?_
  rw [h, inner_smul_left, ← hρ k (ρ k⁻¹ b), ← rho_mul, mul_inv_cancel, map_one, Complex.inv_eq_conj hz]
  rfl

theorem exists_dual [FiniteDimensional ℂ W] (u : W →ₗ[ℂ] ℂ) : ∃ a : W, ∀ w, inner ℂ a w = u w :=
  haveI := FiniteDimensional.complete ℂ W
  ⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap u), fun _ => InnerProductSpace.toDual_symm_apply⟩

theorem exists_linear_section {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (p : X → Y → Prop)
    (h0 : p 0 0) (hadd : ∀ x x' y y', p x y → p x' y' → p (x + x') (y + y')) (hsm : ∀ (a : ℂ) x y, p x y → p (a • x) (a • y))
    (hex : ∀ x, ∃ y, p x y) : ∃ th : X →ₗ[ℂ] Y, ∀ x, p x (th x) := by
  let S : Submodule ℂ (X × Y) :=
    { carrier := {z | p z.1 z.2}
      add_mem' := fun h h' => hadd _ _ _ _ h h'
      zero_mem' := h0
      smul_mem' := fun a _ h => hsm a _ _ h }
  obtain ⟨g, hg⟩ := (LinearMap.fst ℂ X Y ∘ₗ S.subtype).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 fun x => (hex x).elim fun y hy => ⟨⟨(x, y), hy⟩, rfl⟩)
  refine ⟨LinearMap.snd ℂ X Y ∘ₗ S.subtype ∘ₗ g, fun x => ?_⟩
  have h1 : p (g x).1.1 (g x).1.2 := (g x).2
  have h2 : (g x).1.1 = x := LinearMap.congr_fun hg x
  rwa [h2] at h1

theorem scalar_of_form {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) (U : Submodule ℂ Y) (hU : U ≠ ⊥)
    (Λ : ℂ) (h : ∀ y ∈ U, ∀ y', inner ℂ (LinearMap.adjoint th y) (LinearMap.adjoint th y') = Λ * inner ℂ y y') :
    ∀ y ∈ U, th (LinearMap.adjoint th y) = ((‖Λ‖ : ℝ) : ℂ) • y := by
  obtain ⟨y₀, hy₀, h0⟩ := (Submodule.ne_bot_iff _).1 hU
  have e := h y₀ hy₀ y₀
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e
  have hn : ((‖y₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have e1 : Λ = ((‖LinearMap.adjoint th y₀‖ ^ 2 / ‖y₀‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [eq_div_iff (pow_ne_zero 2 hn)]
    exact e.symm
  have e2 : Λ = ((‖Λ‖ : ℝ) : ℂ) := by
    rw [e1, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  intro y hy
  refine ext_inner_right ℂ fun y' => ?_
  rw [← LinearMap.adjoint_inner_right, h y hy, inner_smul_left, Complex.conj_ofReal, ← e2]

end Generic

section Kernel

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (Datum.WO V W → ℂ)} (hω : Datum.IsWeilDatumO ψ V W χS χT ω)
  (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
  (φ : c.W →ₗ[ℂ] (Datum.WO V W → ℂ)) (hφ : ∀ w, Datum.IsThetaFunO ψ V W (φ w))
  (hinf : ∀ u ∈ GinfC V, ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w))
  (hlev : ∀ κ ∈ Lev.levA V (lev D.sp.cm V.gram β L), ∀ w, ω (κ, 1) (φ w) = (Lev.levChi V β L κ)⁻¹ • φ w)

include hω hc hφ hinf hlev in

theorem kernel_law {γ : GA D V} (hγ : γ ∈ GQ V) (k : GA D V) (hk : Lev.finE V k ∈ lev D.sp.cm V.gram β L) (x : GA D V)
    (g : GA D W) (w : c.W) :
    Datum.thetaKO ω (γ * x * k) g (φ w) = (Lev.levChi V β L k)⁻¹ * Datum.thetaKO ω x g (φ (c.ρ k w)) := by
  obtain ⟨κ, h1, h2⟩ := exists_finLift V ((finHom V).rangeRestrict k)
  have h3 : finHom V κ = finHom V k := congrArg Subtype.val h2
  have h4 : Lev.finE V κ = Lev.finE V k := by rw [Lev.finE_eq, Lev.finE_eq, h3]
  have h5 : κ⁻¹ * k ∈ GinfC V := by
    change finHom V (κ⁻¹ * k) = 1
    rw [map_mul, map_inv, h3, inv_mul_cancel]
  have h6 : c.ρ (κ⁻¹ * k) = c.ρ k := by rw [map_mul, hc.1 _ (inv_mem h1), one_mul]
  have h7 : Lev.levChi V β L κ = Lev.levChi V β L k := by unfold Lev.levChi; rw [h4]
  have e : ((γ * x * k, g) : GA D V × GA D W) = (γ, 1) * ((x, g) * ((κ, 1) * (κ⁻¹ * k, 1))) := by
    simp only [Prod.mk_mul_mk, mul_one, one_mul, mul_inv_cancel_left, mul_assoc]
  unfold Datum.thetaKO
  rw [e, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hinf _ h5, h6,
    hlev κ ⟨h1, show Lev.finE V κ ∈ _ from h4 ▸ hk⟩, map_smul, map_smul, Pi.smul_apply, smul_eq_mul,
    hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ (hφ _)), h7]

theorem thetaKO_smul (h : GA D V) (g : GA D W) (a : ℂ) (f : Datum.WO V W → ℂ) :
    Datum.thetaKO ω h g (a • f) = a * Datum.thetaKO ω h g f := by
  unfold Datum.thetaKO
  rw [map_smul]
  rfl

theorem norm_levChi (k : GA D V) : ‖Lev.levChi V β L k‖ = 1 := norm_levFn _ _ _

theorem ext_law {x : Bridge.Gf V → c.W}
    (hx : x ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L)) {γ : GA D V} (hγ : γ ∈ GQ V) (k : GA D V)
    (hk : Lev.finE V k ∈ lev D.sp.cm V.gram β L) (h : GA D V) :
    c.ext x (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (c.ext x h) :=
  form_law (finHom V).rangeRestrict (GQ V) c.ρ hx hγ k ((mem_grpOf V β L k).2 hk) h

theorem ext_finLift (hc : c.Is) (x : Bridge.Gf V → c.W) (u : Bridge.Gf V) : c.ext x (finLift V u) = x u := by
  change c.ρ (finLift V u)⁻¹ (x ((finHom V).rangeRestrict (finLift V u))) = x u
  rw [hc.1 _ (inv_mem (finLift_mem V u)), finLift_spec]
  rfl

include hω hc hφ hinf hlev in

theorem theta_classSum {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V (lev D.sp.cm V.gram β L) ν 𝓕)
    {I : Type} [Fintype I] {y : I → Bridge.Gf V} (hy : Bridge.IsReps (Bridge.ratF V) (grpOf V β L) y)
    {x : Bridge.Gf V → c.W} (hx : x ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L)) (g : GA D W) :
    ∫ h in 𝓕, Datum.thetaKO ω h g (φ (c.ext x h)) ∂ν =
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF V) (grpOf V β L) (y j)) : ℂ))⁻¹ *
        Datum.thetaKO ω (finLift V (y j)) g (φ (x (y j))) := by
  rw [integral_eq_classSum V β L hν hy]
  · simp only [ext_finLift c hc]
  · intro γ hγ k hk h
    rw [kernel_law hω c hc β L φ hφ hinf hlev hγ k hk, ext_law c β L hx hγ k hk, (c.ρ k).map_smul,
      rho_rho_inv c.ρ k, φ.map_smul, thetaKO_smul]
    exact inv_mul_cancel_left₀ (Lev.levChi_ne_zero L k) _

include hω hc hφ hinf hlev in

theorem exists_upVec (μ : Measure (GA D W)) (𝓖 : Set (GA D W)) (F : GA D W → ℂ)
    (hint : ∀ w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) * starRingEnd ℂ (F g)) 𝓖 μ) :
    ∃ Ψ : GA D V → c.W, (∀ h w, inner ℂ (Ψ h) w = l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F) ∧
      ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
        Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h) := by
  have h1 : ∀ h, ∃ a : c.W, ∀ w, inner ℂ a w = l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F := fun h =>
    exists_dual
      { toFun := fun w => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ w)) F
        map_add' := fun w w' => by
          unfold l2 Lift.pet
          rw [← integral_add (hint w h) (hint w' h)]
          simp only [Datum.thetaKO, map_add, Pi.add_apply, add_mul]
        map_smul' := fun a w => by
          unfold l2 Lift.pet
          simp only [Datum.thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
          exact integral_const_mul _ _ }
  choose Ψ hΨ using h1
  refine ⟨Ψ, hΨ, fun γ hγ k hk h => vec_law c.ρ hc.2.1 (norm_levChi β L k) k fun w => ?_⟩
  rw [hΨ, hΨ]
  unfold l2 Lift.pet
  rw [← integral_const_mul]
  congr 1
  funext g
  beta_reduce
  rw [kernel_law hω c hc β L φ hφ hinf hlev hγ k hk, mul_assoc]

end Kernel

theorem l2_sum_eq_sum_norm_sq_of_orthogonal {X I : Type} [MeasurableSpace X] [Fintype I] (μ : Measure X) (𝓖 : Set X) (w : I → ℂ) (k : I → X → ℂ) (F T : X → ℂ)
    (hT : ∀ g, T g = ∑ j, w j * k j g) (hi : ∀ j, IntegrableOn (fun g => k j g * starRingEnd ℂ (F g)) 𝓖 μ) :
    l2 μ 𝓖 T F = ∑ j, w j * l2 μ 𝓖 (k j) F := by
  unfold l2 Lift.pet
  simp only [hT, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ fun j _ => (hi j).const_mul _]
  simp only [integral_const_mul]

theorem l2_eq_star {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓖 : Set X) (F T : X → ℂ) :
    l2 μ 𝓖 T F = ∫ g in 𝓖, star (F g) * T g ∂μ := by
  unfold l2 Lift.pet
  simp only [mul_comm]
  rfl

end GlobalTheory.AdelicScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalConjTrivializationAtPlaceAwayP
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc

variable {p : ℕ} [Fact p.Prime]

theorem glueL_evalT_inC (G : HTGroup p) (w : AwayP p) (c : G.C) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (inC G (AfP p) c) =
      inC G (w.1.adicCompletion ℚ) c := by
  show Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((1 : AfP p) ⊗ₜ c) = (1 : w.1.adicCompletion ℚ) ⊗ₜ c
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem glueL_evalT_starT (G : HTGroup p) (w : AwayP p) (a : AfP p ⊗[ℚ] G.C) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (starT G.star (AfP p) a).unop =
      (starT G.star (w.1.adicCompletion ℚ) (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) a)).unop := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, starT_tmul]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

theorem glueL_evalT_algebraMap (G : HTGroup p) (w : AwayP p) (t : AfP p) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) t) =
      algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (AfP.eval w t) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem glueL_compL_toAfF_fst (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (w : AwayP p) :
    ((((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) :
        w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (x : AfP p ⊗[ℚ] G.C) *
        inC G (w.1.adicCompletion ℚ) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *
        Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
  show Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((x : AfP p ⊗[ℚ] G.C) *
    inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) = _
  rw [map_mul, map_mul, glueL_evalT_inC]

theorem glueL_sh_inv_mul (G : HTGroup p) (c : G.Cˣ) : sh G ((c⁻¹ : G.Cˣ) : G.C) * sh G (c : G.C) = 1 := by
  simp only [sh]
  rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem glueL_main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (g : G.GAf) (c Y : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * Y * ((c⁻¹ : G.Cˣ) : G.C) → ∀ w : AwayP p,
    ∃ (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) (lam : (w.1.adicCompletion ℚ)ˣ),
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = ((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = (((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
        inC G (w.1.adicCompletion ℚ) (β : G.C)) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
  intro p _ G β x t hx y g c Y hy w
  let φ := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  let u : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1
  let ν : (w.1.adicCompletion ℚ)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2
  let xw : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* w.1.adicCompletion ℚ ⊗[ℚ] G.C) x
  let ci : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom c
  let mY : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom Y
  let tw : (w.1.adicCompletion ℚ)ˣ := Units.map (AfP.eval w : AfP p →* w.1.adicCompletion ℚ) t
  have hT : ((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = xw * (ci * mY * ci⁻¹) * xw⁻¹ := by
    apply Units.ext
    rw [glueL_compL_toAfF_fst]
    have hy' : ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) = c * Y * c⁻¹ := Units.ext (by rw [hy]; rfl)
    rw [hy', ← map_inv, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have E : ((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = (u⁻¹ * xw * ci) * mY * (u⁻¹ * xw * ci)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    change u⁻¹ * ((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 * u = _
    rw [hT]
    group
  refine ⟨u⁻¹ * xw * ci, tw * ν⁻¹, ?_, ?_, ?_⟩
  · rw [E]; rfl
  · rw [E, show (u⁻¹ * xw * ci * mY * (u⁻¹ * xw * ci)⁻¹)⁻¹ = (u⁻¹ * xw * ci) * mY⁻¹ * (u⁻¹ * xw * ci)⁻¹ by group]
    rfl
  · have hu : ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) ((ν⁻¹ : (w.1.adicCompletion ℚ)ˣ) : w.1.adicCompletion ℚ) :=
      ((compL G w g)⁻¹).2
    have hxw : φ (x : AfP p ⊗[ℚ] G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) *
        (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) := by
      have h := congrArg φ hx
      rw [map_mul, map_mul, glueL_evalT_inC, glueL_evalT_starT, glueL_evalT_algebraMap] at h
      exact h
    have hs : ∀ z : G.C, (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) z)).unop =
        inC G (w.1.adicCompletion ℚ) (sh G z) := fun z => starT_tmul G.star _ 1 z
    have hC : (c : G.C) * (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β *
        sh G (c : G.C) = β := by
      calc (c : G.C) * (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β *
            sh G (c : G.C)
          = ((c : G.C) * ((c⁻¹ : G.Cˣ) : G.C)) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) *
              (((β⁻¹ : G.Cˣ) : G.C) * β) * sh G (c : G.C) := by simp only [mul_assoc]
        _ = β * (sh G ((c⁻¹ : G.Cˣ) : G.C) * sh G (c : G.C)) := by
            rw [Units.mul_inv, Units.inv_mul, one_mul, mul_one, mul_assoc]
        _ = β := by rw [glueL_sh_inv_mul, mul_one]
    have hk : (((u⁻¹ * xw * ci : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
        ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) * φ (x : AfP p ⊗[ℚ] G.C) *
          inC G (w.1.adicCompletion ℚ) (c : G.C) := rfl
    rw [hk, RingHom.map_mul (starT G.star (w.1.adicCompletion ℚ)), RingHom.map_mul (starT G.star (w.1.adicCompletion ℚ)),
      MulOpposite.unop_mul, MulOpposite.unop_mul, hs]
    calc _ = ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (φ (x : AfP p ⊗[ℚ] G.C) * (inC G (w.1.adicCompletion ℚ) ((c : G.C) *
            (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β * sh G (c : G.C))) *
          (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop := by
          simp only [map_mul, mul_assoc]
      _ = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) *
          (((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop) := by
          rw [hC, hxw, ← mul_assoc, ← Algebra.commutes, mul_assoc]
      _ = _ := by rw [hu, ← map_mul, Units.val_mul]

end GlobalTheory.FinClsLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalComplementEmbeddingHyperbolicPai
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem exists_orthCompl_hypPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
    n = n₁ + 2 → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  intro F E _ _ _ _ _ σ n n₁ J x y hn hJ hxx hyy hxy
  classical
  set a : Fin n → E := J *ᵥ fun i => σ (x i) with ha_def
  set b : Fin n → E := J *ᵥ fun i => σ (y i) with hb_def
  have hfa : ∀ z, form σ J z x = z ⬝ᵥ a := fun z => rfl
  have hfb : ∀ z, form σ J z y = z ⬝ᵥ b := fun z => rfl
  have hxa : x ⬝ᵥ a = 0 := hxx
  have hxb : x ⬝ᵥ b = 1 := hxy
  have ha : a ≠ 0 := by
    intro h0
    have hv : x ᵥ* J = 0 := by
      funext j
      apply σ.toRingHom.injective
      have h1 := congrFun h0 j
      simp only [ha_def, Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, map_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hJ j i, mul_comm]
    apply one_ne_zero (α := E)
    rw [← hxb, hb_def, Matrix.dotProduct_mulVec, hv, zero_dotProduct]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (funext h)
  set w : Fin n → E := (a i)⁻¹ • (Pi.single i 1 - (b i) • x) with hw
  have hwa : w ⬝ᵥ a = 1 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxa, single_dotProduct]
    simp [hi]
  have hwb : w ⬝ᵥ b = 0 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxb, single_dotProduct]
    simp
  let M : Matrix (Fin 2) (Fin n) E := Matrix.of ![a, b]
  have hM : ∀ z, M *ᵥ z = ![z ⬝ᵥ a, z ⬝ᵥ b] := by
    intro z; funext k; fin_cases k <;> simp [M, Matrix.mulVec, dotProduct_comm]
  have hsurj : LinearMap.range (Matrix.mulVecLin M) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨v 0 • w + v 1 • x, ?_⟩
    rw [Matrix.mulVecLin_apply, hM]
    funext k; fin_cases k <;> simp [add_dotProduct, smul_dotProduct, hwa, hwb, hxa, hxb]
  have hrank : Module.finrank E (LinearMap.ker (Matrix.mulVecLin M)) = n₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  set K := LinearMap.ker (Matrix.mulVecLin M) with hK
  have hmemK : ∀ z, z ∈ K ↔ z ⬝ᵥ a = 0 ∧ z ⬝ᵥ b = 0 := by
    intro z
    rw [hK, LinearMap.mem_ker, Matrix.mulVecLin_apply, hM]
    constructor
    · intro h; exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
    · rintro ⟨h1, h2⟩; funext k; fin_cases k <;> simp [h1, h2]
  let bK : Module.Basis (Fin n₁) E K := Module.finBasisOfFinrankEq E K hrank
  let f : (Fin n₁ → E) →ₗ[E] (Fin n → E) := K.subtype ∘ₗ bK.equivFun.symm.toLinearMap
  have hfinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp bK.equivFun.symm.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hfinj
  refine ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · intro u
    rw [LinearMap.toMatrix'_mulVec, hfa, hfb]
    exact (hmemK _).1 (bK.equivFun.symm u).2
  · intro z h1 h2
    have hz : z ∈ K := (hmemK z).2 ⟨h1, h2⟩
    refine ⟨bK.equivFun ⟨z, hz⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    simp [f]

end GlobalTheory
end

