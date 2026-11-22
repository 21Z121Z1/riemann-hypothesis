import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHeckeOpFullOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0213
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0215
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0219
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryRep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.RowsPosRed

theorem exists_unitary_rep {K G V H E : Type} [Field K] [StarRing K] [Group G] [AddCommGroup V] [Module K V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup E] [Module ℂ E] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    {ι : Type} (b : Module.Basis ι K V) (hli : LinearIndependent ℂ fun k => j (b k))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hiso : ∀ x y, ⟪j x, j y⟫_ℂ = σ (h x y)) (r : Representation K G V) (hr : ∀ g x y, h (r g x) (r g y) = h x y)
    (Θ : H →ₗ[ℂ] E) (π : Representation ℂ G E) (hΘ : ∀ g z, Θ (j (r g z)) = π g (Θ (j z))) :
    ∃ ρ : Representation ℂ G H, (∀ g z, j (r g z) = ρ g (j z)) ∧ (∀ g y, ‖ρ g y‖ = ‖y‖) ∧
      ∀ g y, Θ (ρ g y) = π g (Θ y) := by
  let B : Module.Basis ι ℂ H := Module.Basis.mk hli hsp.ge
  have hB : ∀ k, B k = j (b k) := fun k => Module.Basis.mk_apply hli hsp.ge k
  let f : G → Module.End ℂ H := fun g => B.constr ℂ fun k => j (r g (b k))
  have hf : ∀ g z, f g (j z) = j (r g z) := by
    intro g z
    have : (f g).comp j = j.comp (r g) := b.ext fun k => by
      show f g (j (b k)) = j (r g (b k))
      rw [← hB]
      exact B.constr_basis ℂ _ k
    exact LinearMap.congr_fun this z
  let ρ : Representation ℂ G H :=
    { toFun := f
      map_one' := B.ext fun k => by
        show f 1 (B k) = B k
        rw [hB, hf, map_one, Module.End.one_apply]
      map_mul' := fun g g' => B.ext fun k => by
        show f (g * g') (B k) = f g (f g' (B k))
        rw [hB, hf, hf, hf, map_mul, Module.End.mul_apply] }
  have hρ : ∀ g z, ρ g (j z) = j (r g z) := hf
  have hin : ∀ g y y', ⟪ρ g y, ρ g y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
    intro g
    have h1 : ∀ k y', ⟪ρ g (B k), ρ g y'⟫_ℂ = ⟪B k, y'⟫_ℂ := by
      intro k
      have : (innerₛₗ ℂ (ρ g (B k))).comp (ρ g) = innerₛₗ ℂ (B k) := B.ext fun l => by
        show ⟪ρ g (B k), ρ g (B l)⟫_ℂ = ⟪B k, B l⟫_ℂ
        rw [hB, hB, hρ, hρ, hiso, hiso, hr]
      exact fun y' => LinearMap.congr_fun this y'
    intro y y'
    have : (innerₛₗ ℂ (ρ g y)).comp (ρ g) = innerₛₗ ℂ y := B.ext fun l => by
      show ⟪ρ g y, ρ g (B l)⟫_ℂ = ⟪y, B l⟫_ℂ
      rw [← inner_conj_symm, h1, inner_conj_symm]
    exact LinearMap.congr_fun this y'
  refine ⟨ρ, fun g z => (hρ g z).symm, fun g y => ?_, fun g => ?_⟩
  · rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hin]
  · have : Θ.comp (ρ g) = (π g).comp Θ := B.ext fun k => by
      show Θ (ρ g (B k)) = π g (Θ (B k))
      rw [hB, hρ, hΘ]
    exact fun y => LinearMap.congr_fun this y

end GlobalTheory.RowsPosRed

namespace GlobalTheory.RowsPosRed

open Formalism.IndefR.Cx.CxData

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sum_idem_gEx (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2) (x : (R.toCx3 F).EE) :
    ∑ g, A3.A.fam.v0.embedding ((idemOf A3.A.X).coeff g) • R.gEx F g x = x := by
  have h := GlobalTheory.AdjGood.proj_rows_core hC (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x)
  have e : ∀ g, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)
      (A3.A.fam.v0.embedding ((idemOf A3.A.X).coeff g) • R.gEx F g x) =
      D.what₂.embLL ((idemOf A3.A.X).coeff g) • R.gE g (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x) := by
    intro g
    have hc : cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((idemOf A3.A.X).coeff g)) =
        D.what₂.embLL ((idemOf A3.A.X).coeff g) := by
      rw [R.emb0, cj_cj]
    exact congrArg (fun z : ℂ => z • R.gE g (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x)) hc
  exact (Finset.sum_congr rfl fun g _ => e g).trans h

theorem range_le_span_rat {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
    (X : CxData A) (cv : CrdV A) (hK : X.KFormR) (hJ : X.JIsoR cv) (hT : Formalism.IndefR.Rat.RowTest X) (t : Bs.Tup) :
    LinearMap.range (LinearMap.adjoint (X.Θ t)) ≤
      Submodule.span ℂ (X.jR t '' {z | X.jR t z ∈ LinearMap.range (LinearMap.adjoint (X.Θ t))}) := by
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  exact (Formalism.IndefR.Rat.range_adjoint_rat _ (X.jR t) (cv.hR t) (bR t) (hK t).1 (hK t).2 (hJ t) (X.Θ t) ψ hψ
    (fun i x => hr t i x)).ge

theorem exists_rho (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hM : R.toRealDat.IsModels)
    (hGE : R.PGEquiv F) :
    ∃ ρ : Representation ℂ G ((R.toCx3 F).FC A3.A.fam.μ0),
      (∀ g z, (R.toCx3 F).jR A3.A.fam.μ0 ((A3.A.fam.R A3.A.fam.μ0).r g z) = ρ g ((R.toCx3 F).jR A3.A.fam.μ0 z)) ∧
      (∀ g y, ‖ρ g y‖ = ‖y‖) ∧
      ∀ g y, (R.toCx3 F).Θ A3.A.fam.μ0 (ρ g y) = R.gEx F g ((R.toCx3 F).Θ A3.A.fam.μ0 y) := by
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hM
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hM
  exact exists_unitary_rep (V := (A3.A.fam.R A3.A.fam.μ0).S.Forms) (H := (R.toCx3 F).FC A3.A.fam.μ0)
    ((R.toCx3 F).jR A3.A.fam.μ0) (Formalism.IndefR.Cx.CxData.bR (A := A3.fam3.amb3) A3.A.fam.μ0) (hKR A3.A.fam.μ0).1
    (hKR A3.A.fam.μ0).2 (F.cv.hR A3.A.fam.μ0) (hJR A3.A.fam.μ0) (A3.A.fam.R A3.A.fam.μ0).r
    (fun g x y => (hOk.ok2.what₂ A3.A.fam.μ0).act.unitary g x y) ((R.toCx3 F).Θ A3.A.fam.μ0) (R.gEx F)
    (fun g z => hGE.1 A3.A.fam.μ0 g z)

theorem exists_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hM : R.toRealDat.IsModels) (hN : RowsNe R.toRealDat F.lv2)
    (b : Bool) : ∃ u : (R.toCx3 F).EE, u ≠ 0 ∧ u ∈ (R.toCx3 F).EEl b := by
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 (hN b)
  have hT : U ∈ R.EEat R.triv := GlobalTheory.GoodRowsLevel.eeat_le_triv R.toRealDat _ hU
  obtain ⟨y, rfl⟩ : U ∈ LinearMap.range R.HE.e := hM.HE.2.1 ▸ hT
  refine ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) y, fun h0 => hU0 ?_, hU⟩
  have : y = 0 := h0
  rw [this, map_zero]

omit [Fintype G] in

theorem tw_eq_zero {s : Bool} {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (f : E →ₗ[ℂ] E')
    (hf : Function.Injective (LinearMap.adjoint f)) (v : Tw s E') (h1 : ∀ y : Tw s E, ⟪Tw.map s f y, v⟫_ℂ = 0) : v = 0 := by
  have h5 : LinearMap.adjoint f (Tw.out v) = 0 := by
    refine ext_inner_left ℂ fun y => ?_
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    have h3 : cj s ⟪f y, Tw.out v⟫_ℂ = 0 := h1 (Tw.mk s y)
    have h4 := congrArg (cj s) h3
    rwa [cj_cj, map_zero] at h4
  exact hf (h5.trans (map_zero _).symm)

theorem surj_of_upInj (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hUp : UpInj R.toRealDat) (x : (R.toCx3 F).EE) :
    ∃ u, (R.toCx3 F).Θ A3.A.fam.μ0 (LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) u) = x := by
  have hinj : ∀ v, LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v = 0 → v = 0 := by
    intro v hv
    have h1 : ∀ y : (R.toCx3 F).FC A3.A.fam.μ0, ⟪(R.toCx3 F).Θ A3.A.fam.μ0 y, v⟫_ℂ = 0 := fun y => by
      rw [← LinearMap.adjoint_inner_right, hv, inner_zero_right]
    exact tw_eq_zero (s := twAt D.what₂.embLL A3.A.v0) (R.Th A3.A.fam.μ0) (hUp A3.A.fam.μ0) v h1
  have h2 : Function.Injective ((R.toCx3 F).Θ A3.A.fam.μ0 ∘ₗ LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h3 : ⟪LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v, LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0) v⟫_ℂ = 0 := by
      rw [LinearMap.adjoint_inner_left]
      rw [LinearMap.comp_apply] at hv
      rw [hv, inner_zero_right]
    exact hinj v (inner_self_eq_zero.1 h3)
  exact LinearMap.injective_iff_surjective.1 h2 x

theorem dZ_pos_of_row (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F)
    (hEx : R.toRealDat.ExAt) (hUp : UpInj R.toRealDat) (hGE : R.PGEquiv F) (hRT : Formalism.IndefR.Rat.RowTest (R.toCx3 F))
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (u : (R.toCx3 F).EE) (hu0 : u ≠ 0)
    (hu : u ∈ typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ) :
    0 < (A3.A.fam.R A3.A.fam.μ0).dZ (A3.A.fam.lvl P ψ) ((R.toCx3 F).Z A3.A.fam.μ0) := by
  have hM : R.toRealDat.IsModels := hC.base.models
  have hrat := range_le_span_rat (R.toCx3 F) F.cv (RealDat3.kFormR_of hM) (RealDat3.jIsoR_of hM) hRT A3.A.fam.μ0
  obtain ⟨ρ, hj, hρ, hΘ⟩ := exists_rho R F hOk hM hGE
  have hCore := (GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx).1
  have htype : ∀ h : P, R.gEx F (h : G) u = A3.A.fam.v0.embedding ((ψ h : D.what₂.LLˣ) : D.what₂.LL) • u := by
    intro h
    have := (Submodule.mem_iInf _).1 hu h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨w, hw⟩ := surj_of_upInj R F hUp u
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.RowsNonzero.exists_rational ((R.toCx3 F).jR A3.A.fam.μ0) (A3.A.fam.R A3.A.fam.μ0).r ρ
    (R.gEx F) ((R.toCx3 F).Θ A3.A.fam.μ0) hj hρ hΘ hrat (fun g => (idemOf A3.A.X).coeff g)
    (fun g => (lvlIdem P ψ).coeff g) hu0 hw (sum_idem_gEx R F hCore u)
    (GlobalTheory.RowsNonzero.sum_lvlIdem (R.gEx F) P ψ htype)
  exact GlobalTheory.RowsNonzero.dZ_pos (A3.A.fam.R A3.A.fam.μ0) (A3.A.fam.lvl P ψ) ((R.toCx3 F).Z A3.A.fam.μ0) hz0 hz

end GlobalTheory.RowsPosRed

theorem GlobalTheory.RowsPosRed.pos_of_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInj R.toRealDat → RowsNe R.toRealDat F.lv2 → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hUp hNe hGE _ hRT b
  have hel := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.RowsPosRed.exists_row R F hC.base.models hNe b
  cases b
  · rw [hel.1] at hu
    exact GlobalTheory.RowsPosRed.dZ_pos_of_row R F hOk hC hEx hUp hGE hRT F.P0 F.ψ0 u hu0 hu
  · rw [hel.2] at hu
    exact GlobalTheory.RowsPosRed.dZ_pos_of_row R F hOk hC hEx hUp hGE hRT F.P1 F.ψ1 u hu0 hu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarily
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
open Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Bridge Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteGroupUnitary

theorem isUnitaryRep_of_norm {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Representation ℂ G H) (h : ∀ g x, ‖ρ g x‖ = ‖x‖) : IsUnitaryRep ρ := by
  intro g x y
  let e : H →ₗᵢ[ℂ] H := ⟨ρ g, h g⟩
  exact e.inner_map_map x y

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

theorem pairAt_eq_of_rat (x y : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) : pairAt S σ x y = σ (S.pair x y) := by

  have hexp : S.pair x y = ∑ i, ∑ j, star (S.bV.repr x i) * S.gramV i j * S.bV.repr y j := by
    conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, CSD.gramV, Matrix.of_apply,
      starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexp]
  simp only [pairAt, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_

  have hc : ∀ τ : K →+* ℂ, τ (star (S.bV.repr x i)) = starRingEnd ℂ (τ (S.bV.repr x i)) := hx i
  rw [hc σ]

theorem csumAt_eq_of_rat (f f' : S.Cl → S.V) (hf : S.IsRat f) : csumAt S σ f f' = σ (S.csum f f') := by
  simp only [csumAt, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pairAt_eq_of_rat S σ (f c) (f' c) (fun i => hf c i)]

theorem csumAt_add_left (f g f' : S.Cl → S.V) : csumAt S σ (f + g) f' = csumAt S σ f f' + csumAt S σ g f' := by
  simp only [csumAt, pairAt, Pi.add_apply, map_add, Finsupp.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

theorem csumAt_smul_left (a : K) (f f' : S.Cl → S.V) :
    csumAt S σ (a • f) f' = starRingEnd ℂ (σ a) * csumAt S σ f f' := by
  simpa using csumAt_smul S σ a 1 f f'

private theorem csumAt_add_right (f g g' : S.Cl → S.V) :
    csumAt S σ f (g + g') = csumAt S σ f g + csumAt S σ f g' := by
  simp only [csumAt, pairAt, Pi.add_apply, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

private theorem csumAt_smul_right' (b : K) (f f' : S.Cl → S.V) :
    csumAt S σ f (b • f') = σ b * csumAt S σ f f' := by
  simpa using csumAt_smul S σ 1 b f f'

private theorem csumAt_sum_left {ι : Type} (s : Finset ι) (F : ι → S.Cl → S.V) (f' : S.Cl → S.V) :
    csumAt S σ (∑ i ∈ s, F i) f' = ∑ i ∈ s, csumAt S σ (F i) f' := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [csumAt, pairAt]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, csumAt_add_left, ih]

private theorem csumAt_sum_right {ι : Type} (s : Finset ι) (f : S.Cl → S.V) (F : ι → S.Cl → S.V) :
    csumAt S σ f (∑ i ∈ s, F i) = ∑ i ∈ s, csumAt S σ f (F i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [csumAt, pairAt]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, csumAt_add_right, ih]

theorem csumAt_map (hb : S.HasRatBasis) (U : Module.End K S.Forms)
    (hU : ∀ f : S.Forms, S.IsRat (f : S.Cl → S.V) → S.IsRat (U f : S.Cl → S.V))
    (hc : ∀ f f' : S.Forms, S.csum (U f : S.Cl → S.V) (U f' : S.Cl → S.V) = S.csum (f : S.Cl → S.V) (f' : S.Cl → S.V))
    (f f' : S.Forms) :
    csumAt S σ (U f : S.Cl → S.V) (U f' : S.Cl → S.V) = csumAt S σ (f : S.Cl → S.V) (f' : S.Cl → S.V) := by
  obtain ⟨b, hbr⟩ := hb

  have key : ∀ i j, csumAt S σ (U (b i) : S.Cl → S.V) (U (b j) : S.Cl → S.V) =
      csumAt S σ (b i : S.Cl → S.V) (b j : S.Cl → S.V) := by
    intro i j
    rw [csumAt_eq_of_rat S σ _ _ (hU _ (hbr i)), csumAt_eq_of_rat S σ _ _ (hbr i), hc]

  rw [← b.sum_repr f, ← b.sum_repr f']
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, csumAt_sum_left, csumAt_sum_right,
    csumAt_smul_left, csumAt_smul_right', key]

end ClassSum

section Presented

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}

theorem adInner_g0Act (l : LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : IsReps ι l.J y) (κ : l.Q) {F F' : G → W}
    (hF : F ∈ AdForms ι ρ l.J l.χ) (hF' : F' ∈ AdForms ι ρ l.J l.χ) :
    adInner ι l.J y (g0Act l.ch κ F) (g0Act l.ch κ F') = adInner ι l.J y F F' := by

  have hκ : ∀ k, (κ : G)⁻¹ * k * κ ∈ l.J ↔ k ∈ l.J := by
    intro k
    constructor
    · intro hk
      have h2 := hn (κ : G)⁻¹ (l.Q.inv_mem κ.2) _ hk
      have e : ((κ : G)⁻¹)⁻¹ * ((κ : G)⁻¹ * k * κ) * (κ : G)⁻¹ = k := by group
      rwa [e] at h2
    · intro hk
      exact hn κ κ.2 k hk
  have hχ : ∀ k : l.J, ‖(l.χ k : ℂ)‖ = 1 := fun k => by rw [← l.ch_J k]; exact hch _

  have hy' := GlobalTheory.ClassSumTranslate.isReps_mul ι hκ hy
  rw [← GlobalTheory.ClassSumTranslate.adInnerIndep ι ρ l.J l.χ hρ hχ I I (fun i => y i * κ) y hy' hy F hF F' hF']
  have hn1 : ‖(((l.ch κ)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hch κ, inv_one]
  have hc : starRingEnd ℂ (((l.ch κ)⁻¹ : ℂˣ) : ℂ) * (((l.ch κ)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [RCLike.conj_mul, hn1]
    simp
  unfold adInner g0Act
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.ClassSumTranslate.stab_mul ι hκ (y i), inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _), hc,
    one_mul]

theorem isUnitaryAtAll_of_tie (l : LevDatG G) (P : ClassPres ι S σ₀ ρ l.J l.χ) {G₀ : Type} [Group G₀]
    (act : Representation K G₀ S.Forms) (T : ActTie ι P l.Q l.ch act)
    (hσ : ∀ a : K, σ₀ (star a) = starRingEnd ℂ (σ₀ a))
    (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ∃ n : ℕ, 0 < n ∧ l.ch q ^ n = 1)
    (hrat : ∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ₀ (c i) • P.coef (S.bV i)) :
    IsUnitaryAtAll S act := by

  have hchn : ∀ q, ‖(l.ch q : ℂ)‖ = 1 := by
    intro q
    obtain ⟨n, hn, hq⟩ := hch q
    have h1 : (l.ch q : ℂ) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, hq, Units.val_one]
    have h2 : ‖(l.ch q : ℂ)‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2
  have hχ : ∀ k, ∃ n : ℕ, 0 < n ∧ l.χ k ^ n = 1 := by
    intro k
    obtain ⟨n, hn, hk⟩ := hch ⟨k, l.J_le k.2⟩
    exact ⟨n, hn, by rw [← l.ch_J k]; exact hk⟩

  have hb : S.HasRatBasis := by
    refine (GlobalTheory.classPres_dcOp_rat ι S σ₀ ρ l.J l.χ P {1} 1 hσ hχ hrat ?_).1
    intro f
    funext h
    simp [dcOp]
  intro σ g f f'
  obtain ⟨κ, hκ⟩ := T.red_surj g
  refine csumAt_map S σ hb (act g) ?_ ?_ f f'
  ·

    intro f hf c i
    rw [← GlobalTheory.PresRat.mem_cmComplex_iff σ₀ hσ, ← GlobalTheory.PresBasic.repr_coef P, ← GlobalTheory.PresBasic.ext_y P, T.act_eq g κ hκ f]
    have hd := P.dec_spec (P.y c * (κ : G))
    unfold g0Act
    rw [hd, GlobalTheory.PresBasic.ext_dec P, map_smul, Finsupp.smul_apply, smul_eq_mul]
    refine mul_mem ?_ (GlobalTheory.PresRat.act_mem P hσ hχ hrat _ _ _ (fun j => hf _ j) i)
    obtain ⟨n, hn, hq⟩ := hch κ
    refine GlobalTheory.PresRat.mem_cmComplex_of_pow hn ?_
    rw [← Units.val_pow_eq_pow_val, inv_pow, hq, inv_one, Units.val_one]
  ·
    intro f f'
    apply σ₀.injective
    have e1 := GlobalTheory.PresBasic.isom P (act g f) (act g f')
    have e2 := GlobalTheory.PresBasic.isom P f f'
    rw [← e1, ← e2, T.act_eq g κ hκ f, T.act_eq g κ hκ f']
    exact adInner_g0Act l hρ hn hchn P.reps κ (GlobalTheory.PresBasic.extMem P f) (GlobalTheory.PresBasic.extMem P f')

end Presented

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levEnv_ch_pow (V : TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) : ∃ n : ℕ, 0 < n ∧ (levEnv V β L).ch q ^ n = 1 := by

  obtain ⟨n, hn, hx⟩ := isOfFinOrder_iff_pow_eq_one.1 (GlobalTheory.HeckeRational.levFn_isOfFinOrder β (Formalism.IndefR.Lev.flagL L)
    (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) q.1.1))
  refine ⟨n, hn, ?_⟩
  have e : (levEnv V β L).ch q = Formalism.L2.DIV.levFn β (Formalism.IndefR.Lev.flagL L)
      (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) q.1.1) := rfl
  rw [e, hx]

theorem definiteUnitary (R : RealDat D A Ks) (h : R.fam_tie) (hX : R.models_cX) (hV : R.models_cV) : DefiniteUnitary A := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  refine ⟨fun t => ?_, fun i t => ?_⟩
  ·
    exact isUnitaryAtAll_of_tie (levEnv D.sp.X' R.βX (R.datXt t)) (R.B.R t).pres (A.leftGroupActionRight t) (R.B.R t).act_tie
      D.starLL_cx (fun γ x x' => hX.2.1 _ x x') (GlobalTheory.ClassSumTranslate.levEnv_normal _ _ _) (levEnv_ch_pow _ _ _)
      (fun γ j => GlobalTheory.HeckeRational.action_rational _ _ (R.B.R t).pres (hT.coefR t) hT.mapR
        (fun g a b => (GlobalTheory.coefAction_repr_mem_subfield _ (cmMax D.what₂.LL) _
          (fun τ x => GlobalTheory.HeckeRational.labLL_mem_cmMax τ x) g a b).1) γ j)
  ·
    exact isUnitaryAtAll_of_tie (levEnv (Vc D i) (R.βV i) (R.datVt i t)) (R.B.L i t).pres (A.leftGroupActionLift i t) (R.B.L i t).act_tie
      D.starLL_cx (fun γ x x' => (hV i).2.1 _ x x') (GlobalTheory.ClassSumTranslate.levEnv_normal _ _ _) (levEnv_ch_pow _ _ _)
      (fun γ j => GlobalTheory.HeckeRational.action_rational _ _ (R.B.L i t).pres (hT.coefL i t) (hT.mapL i)
        (fun g a b => (GlobalTheory.coefAction_repr_mem_subfield _ (cmMax D.what₂.LL) _
          (fun τ x => GlobalTheory.HeckeRational.labLL_mem_cmMax τ x) g a b).2) γ j)

end GlobalTheory.FiniteGroupUnitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlacesStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), (∀ v : HeightOneSpectrum (𝓞 F), Finite (Cls P (Fv F v))) ∧ ∀ w : InfinitePlace F, Finite (Cls P w.Completion) := by
  first | exact @GlobalTheory.SqCls.finite_cls | exact GlobalTheory.SqCls.finite_cls | (intros; apply GlobalTheory.SqCls.finite_cls <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorMaximalCompactMovedBasesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialVector_maximalCompact_moved_bases : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), BS' τ = BS τ * κS → BT' τ = BT τ * κT → (∀ ρ, ρ ≠ τ → BS' ρ = BS ρ ∧ BT' ρ = BT ρ) → ∀ P, pureTensorO ψ θ S T sS sT BS' BT' f P = pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  first | exact @GlobalTheory.FockSubBoth.pureTensorO_fockSub | exact GlobalTheory.FockSubBoth.pureTensorO_fockSub | (intros; apply GlobalTheory.FockSubBoth.pureTensorO_fockSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSourceGlActionEqQuadraticAddNonRaisingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSourceGlAction_eq_quadratic_add_nonRaising : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (X : Matrix (Fin a) (Fin a) ℂ), 0 < b → (∃ j k, ε j ≠ ε k ∧ X j k ≠ 0 ∧ X k j ≠ 0) → ∃ (Q : PolF D b a) (L : Module.End ℂ (PolF D b a)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' X = LinearMap.mulLeft ℂ Q + L := by
  first | exact @GlobalTheory.Chain.RealIt.FockSrcDec.fockS_decomp | exact GlobalTheory.Chain.RealIt.FockSrcDec.fockS_decomp | (intros; apply GlobalTheory.Chain.RealIt.FockSrcDec.fockS_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockTargetGlActionEqQuadraticAddNonRaisingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockTargetGlAction_eq_quadratic_add_nonRaising : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin b) (Fin b) ℂ), 0 < a → (∃ i l, ε' i ≠ ε' l ∧ Y i l ≠ 0 ∧ Y l i ≠ 0) → ∃ (Q : PolF D b a) (L : Module.End ℂ (PolF D b a)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y = LinearMap.mulLeft ℂ Q + L := by
  first | exact @GlobalTheory.Chain.FockTDec.fockT_decomp | exact GlobalTheory.Chain.FockTDec.fockT_decomp | (intros; apply GlobalTheory.Chain.FockTDec.fockT_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussians
section
open MeasureTheory

namespace GlobalTheory.FockFamily

theorem fock_vacua_family : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ J : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) → (∀ t w, J t (J t w) = -w) →
    (∀ t, ∃ g : SchwartzMap V ℂ, g ≠ 0 ∧ ∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
    ∃ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => M p.1 p.2 p.2) ∧
      (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) ∧
      (∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
        ∀ x, g x = g 0 * Complex.exp (M t x x)) ∧
      ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
        HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  intro V _ _ _ β hβ J hJ _ hex
  choose g0 hg0ne hg0 using hex
  have hunit : ∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t)) := fun t =>
    GlobalTheory.T.isUnit_upperRightBlock_of_heisenbergDerivative_solution β hβ (J t) (g0 t) (g0 t).continuous (fun h => hg0ne t (SchwartzMap.ext (fun x => congrFun h x))) (hg0 t)
  obtain ⟨hB, hD⟩ := GlobalTheory.T.contDiff_prodLinearMap_upperRight_lowerRight_blocks J hJ
  obtain ⟨hsm, hjoint⟩ := GlobalTheory.T.contDiff_fockGaussianFormOfLinearMap_family β J hB hD hunit
  have hray : ∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x =
      Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) → ∀ x, g x = g 0 * Complex.exp (GlobalTheory.FockFamily.fockForm β (J t) x x) :=
    fun t g hg => GlobalTheory.T.eq_exp_fockGaussianForm_of_heisenbergDerivative_eq β (J t) (hunit t) g g.differentiable hg
  refine ⟨fun t => GlobalTheory.FockFamily.fockForm β (J t), hsm, hjoint, ?_, hray, ?_⟩
  · exact GlobalTheory.T.uniformly_negDefinite_near_of_continuous_quadForm_family (fun t => GlobalTheory.FockFamily.fockForm β (J t)) hjoint.continuous
      (fun t v hv => GlobalTheory.T.gaussian_form_re_neg_of_ne_zero _ (g0 t) (hg0ne t) (hray t (g0 t) (hg0 t)) v hv)
  · exact GlobalTheory.T.exists_hasDerivAt_diag_eq_sum_mul_pairings β hβ _ (fun x y => ((hsm x y).differentiable (by simp)).differentiableAt)

end GlobalTheory.FockFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlueSmoothOfCompactSupportStatement
section
open GlobalTheory.Orb
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_contDiff_comp_of_locally_smooth_compactSupport : ∀ (H : Type) [TopologicalSpace H] (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (c : H → X) (f : H → ℂ), Continuous c → HasCompactSupport f → (∀ a, ∃ V : Set X, IsOpen V ∧ c a ∈ V ∧ ∃ Φ : X → ℂ, ContDiffOn ℝ ∞ Φ V ∧ ∀ g, c g ∈ V → f g = Φ (c g)) → ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) := by
  first | exact @GlobalTheory.glue_smooth_of_compactSupport | exact GlobalTheory.glue_smooth_of_compactSupport | (intros; apply GlobalTheory.glue_smooth_of_compactSupport <;> assumption)
end

