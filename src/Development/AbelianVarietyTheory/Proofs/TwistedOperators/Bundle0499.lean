import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0213
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0494
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarHeckeTraceThetaGeneratorFamily
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRangeRestrictEq
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftEquivariance

theorem commutes_adjoint {G E E' : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
    (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hρ' : ∀ g x, ‖ρ' g x‖ = ‖x‖)
    (f : E →ₗ[ℂ] E') (hf : Commutes ρ ρ' f) : Commutes ρ' ρ (LinearMap.adjoint f) := by
  intro g y
  have i1 : ∀ u v, inner ℂ (ρ g u) (ρ g v) = inner ℂ u v :=
    fun u v => (LinearIsometry.mk (ρ g) (hρ g)).inner_map_map u v
  have i2 : ∀ u v, inner ℂ (ρ' g u) (ρ' g v) = inner ℂ u v :=
    fun u v => (LinearIsometry.mk (ρ' g) (hρ' g)).inner_map_map u v
  refine ext_inner_left ℂ fun x => ?_
  have e : x = ρ g (ρ g⁻¹ x) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e, i1, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right, hf g, i2]

section Generic

variable {Γ Gf W G : Type} [Group Γ] [Group Gf] [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem translate_indep (ι : Γ →* Gf) (ρ : Γ →* Module.End ℂ W) (l : Bridge.LevDatG Gf) {F : Gf → W}
    (hF : F ∈ Bridge.AdForms ι ρ l.J l.χ) (κ κ' : l.Q) (hk : ((κ⁻¹ * κ' : l.Q) : Gf) ∈ l.J) (h : Gf) :
    (((l.ch κ')⁻¹ : ℂˣ) : ℂ) • F (h * κ') = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * κ) := by
  have e := hF 1 (h * κ) ⟨_, hk⟩
  have e1 : ι 1 * (h * κ) * ((κ⁻¹ * κ' : l.Q) : Gf) = h * κ' := by simp [mul_assoc]
  have e2 : l.χ ⟨_, hk⟩ = (l.ch κ)⁻¹ * l.ch κ' := by
    rw [← l.ch_J, ← map_inv, ← map_mul]
  simp only at e
  rw [e1, e2, map_one, Module.End.one_apply] at e
  rw [e, smul_smul, ← Units.val_mul, mul_comm (l.ch κ)⁻¹, inv_mul_cancel_left]

theorem exists_rep (ι : Γ →* Gf) (ρ : Γ →* Module.End ℂ W) (l : Bridge.LevDatG Gf) (M : HMod (Gf → W))
    (hinj : Function.Injective M.e) (hM : ∀ x, M.e x ∈ Bridge.AdForms ι ρ l.J l.χ)
    (hT : ∀ (κ : l.Q) (x : M.H), ∃ x' : M.H, (∀ h, M.e x' h = ((l.ch κ : ℂˣ) : ℂ)⁻¹ • M.e x (h * κ)) ∧ ‖x'‖ = ‖x‖)
    (red : l.Q →* G) (hs : Function.Surjective red) (hker : ∀ κ, red κ = 1 → (κ : Gf) ∈ l.J) :
    ∃ π : Representation ℂ G M.H, (∀ g x, ‖π g x‖ = ‖x‖) ∧
      ∀ κ x h, M.e (π (red κ) x) h = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • M.e x (h * κ) := by
  choose s hs using hs
  choose T hT hn using hT
  have key : ∀ κ x h, M.e (T (s (red κ)) x) h = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • M.e x (h * κ) := fun κ x h => by
    rw [hT, ← Units.val_inv_eq_inv_val]
    exact translate_indep ι ρ l (hM x) κ _ (hker _ (by rw [map_mul, map_inv, hs, inv_mul_cancel])) h
  let L : G → M.H →ₗ[ℂ] M.H := fun g =>
    { toFun := T (s g)
      map_add' := fun x y => hinj (funext fun h => by
        rw [map_add, Pi.add_apply, hT, hT, hT, map_add, Pi.add_apply, smul_add])
      map_smul' := fun a x => hinj (funext fun h => by
        rw [map_smul, Pi.smul_apply, hT, hT, map_smul, Pi.smul_apply, smul_comm]; rfl) }
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := fun g g' => ?_ }, fun g x => hn _ x, key⟩
  · ext x
    refine hinj (funext fun h => ?_)
    have := key 1 x h
    rw [map_one] at this
    exact this.trans (by simp)
  · ext x
    refine hinj (funext fun h => ?_)
    have := key (s g * s g') x h
    rw [map_mul, hs, hs] at this
    refine this.trans ?_
    show _ = M.e (T (s g) (T (s g') x)) h
    rw [hT, hT, smul_smul, map_mul, Subgroup.coe_mul, mul_assoc]
    simp [mul_comm]

end Generic

variable {D : D7}

theorem mem_parLev {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x : Bridge.Gf V}
    (h : x ∈ (levEnv V β L).Q) : Formalism.UG.bc (swapAE D) x.1 ∈ parLev D.sp.cm V.gram β L := by
  have h1 : Formalism.UG.bc (swapAE D) x.1 ∈ lev D.sp.cm V.gram β (flagL L) := h
  exact h1.1

theorem mem_J {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x : Bridge.Gf V}
    (h : x ∈ (levEnv V β L).Q) (h1 : rTup β L (Formalism.UG.bc (swapAE D) x.1) = 1) : x ∈ (levEnv V β L).J := by
  have h2 : rTup β L (Formalism.UG.bc (swapAE D) x.1) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := Subgroup.mem_bot.2 h1
  have h3 : Formalism.UG.bc (swapAE D) x.1 ∈ lev D.sp.cm V.gram β (flag1L L) := ⟨mem_parLev h, h2⟩
  exact h3

theorem rTup_bc_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x y : Bridge.Gf V}
    (hx : x ∈ (levEnv V β L).Q) (hy : y ∈ (levEnv V β L).Q) :
    rTup β L (Formalism.UG.bc (swapAE D) (x * y).1) =
      rTup β L (Formalism.UG.bc (swapAE D) x.1) * rTup β L (Formalism.UG.bc (swapAE D) y.1) := by
  rw [Subgroup.coe_mul, map_mul]
  exact rTup_mul (mem_parLev hx) (mem_parLev hy)

def redHom (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    (levEnv V β L).Q →* G0 L.Pg L.r :=
  MonoidHom.mk' (fun κ => rTup β L (Formalism.UG.bc (swapAE D) κ.1.1)) fun a b => rTup_bc_mul a.2 b.2

theorem redHom_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {κ : (levEnv V β L).Q}
    {g₀ : G0 L.Pg L.r} : LiftsTo V β L κ g₀ ↔ redHom V β L κ = g₀ := Iff.rfl

theorem exists_transRep (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V) (hc : c.Is)
    (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    {G : Type} [Group G] (eG : G ≃* G0 L.Pg L.r) (hs : ∀ g, ∃ κ, LiftsTo V β L κ (eG g)) :
    ∃ π : Representation ℂ G M.H, (∀ g x, ‖π g x‖ = ‖x‖) ∧ IsTransRep V β L eG M π := by
  have hred : ∀ κ g, LiftsTo V β L κ (eG g) → (eG.symm.toMonoidHom.comp (redHom V β L)) κ = g := fun κ g h =>
    eG.symm_apply_eq.2 (redHom_eq.1 h)
  have h1 : ∀ x, M.e x ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L).J (levEnv V β L).χ :=
    fun x => hM.2.1.le ⟨x, rfl⟩
  have h2 := ClassSumTranslate.translate_model (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L)
    (fun γ u v => hc.2.1 _ u v) (ClassSumTranslate.levEnv_normal V β L) (fun q => ClassSumTranslate.norm_levFn V β L _) hy M hM
  have h3 : Function.Surjective (eG.symm.toMonoidHom.comp (redHom V β L)) := fun g => (hs g).imp fun κ h => hred κ g h
  have h4 : ∀ κ, (eG.symm.toMonoidHom.comp (redHom V β L)) κ = 1 → (κ : Bridge.Gf V) ∈ (levEnv V β L).J := fun κ h =>
    mem_J κ.2 (redHom_eq.2 (eG.symm.injective (h.trans (map_one eG.symm).symm)))
  refine (exists_rep (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L) M hM.1 h1 h2 _ h3 h4).imp
    fun π hπ => ⟨hπ.1, fun g x => ⟨hs g, fun κ hκ h => ?_⟩⟩
  exact (congrArg (fun g' => M.e (π g' x) h) (hred κ g hκ)).symm.trans (hπ.2 κ x h)

theorem exists_rangeRestrict_eq {G H : Type} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (h : ∀ g, ∃ a ∈ f.ker, ∃ k ∈ K, g = a * k) (x : f.range) : ∃ k ∈ K, f.rangeRestrict k = x := by
  obtain ⟨_, g, rfl⟩ := x
  obtain ⟨a, ha, k, hk, rfl⟩ := h g
  refine ⟨k, hk, Subtype.ext ?_⟩
  show f k = f (a * k)
  rw [map_mul, MonoidHom.mem_ker.1 ha, one_mul]

theorem exists_fin_lift (V : HSp D) (x : Bridge.Gf V) : ∃ k ∈ GfC V, (finHom V).rangeRestrict k = x :=
  exists_rangeRestrict_eq (finHom V) (GfC V) (GlobalTheory.UnitarySplit.real_finite_split D V).1 x

theorem ch_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (q : (levEnv V β L).Q) :
    (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) q.1.1) := rfl

theorem exists_adelic_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {g₀ : G0 L.Pg L.r} {F F' : Bridge.Gf V → W}
    (h : IsTranslate V β L g₀ F F') :
    ∃ κ, IsLevelLift V β L g₀ κ ∧ ∀ x, F' x = (levChi V β (flagL L) κ)⁻¹ • F (x * (finHom V).rangeRestrict κ) := by
  refine h.1.elim fun q hl => (exists_fin_lift V q.1).imp fun k hk => ?_
  have e0 : finHom V k = q.1.1 := congrArg Subtype.val hk.2
  have e1 : finE V k = Formalism.UG.bc (swapAE D) q.1.1 := (finE_eq V k).trans (congrArg (Formalism.UG.bc (swapAE D)) e0)
  have hl1 : rTup β L (Formalism.UG.bc (swapAE D) q.1.1) = g₀ := hl
  have hc : levChi V β (flagL L) k = (((levEnv V β L).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans (ch_eq q).symm)
  have hp : finE V k ∈ parLev D.sp.cm V.gram β L := e1.symm ▸ mem_parLev q.2
  refine ⟨⟨hk.1, hp, (congrArg (rTup β L) e1).trans hl1⟩, fun x => (h.2 q hl x).trans ?_⟩
  exact congrArg₂ (fun (a : ℂ) (z : Bridge.Gf V) => a • F (x * z))
    ((Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hc.symm)) hk.2.symm

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end GlobalTheory.LiftEquivariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalHomApproxHalfModIdealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_hom_approx_half_mod_ideal : ∀ {D : D7} {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ → Submodule.IsLattice D.host.E Λ → Submodule.IsLattice D.host.E Λ' → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → ∀ z : Mx D m n, IsHalf e z → z ∈ hatMx (homLat Λ Λ') → ∃ x₁ : homLat Λ Λ', z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ') := by
  first | exact @GlobalTheory.CosRatApprox.exists_rat_approx | exact GlobalTheory.CosRatApprox.exists_rat_approx | (intros; apply GlobalTheory.CosRatApprox.exists_rat_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarHeckeTraceThetaGeneratorFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_heckeTrace_thetaGenerator_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i n : ℕ) (T : Type) [CommRing T] [IsReduced T] [Algebra c.F T] (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (σ : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (s₀ : LB.Sec (PPx x')), admitted l P p → IsHeckeFam P p i Ψ → IsListed Ψ σ → SecGen x' s₀ → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁'), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → ∃ s', IsThGen x₁' s' ∧ IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s') → ∃ a : T, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁') (s' : LB.Sec (PPx x₁')), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → IsThGen x₁' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s' → SecBC χ.toRingHom a x' x₁' s₀ s' := by
  first | exact @GlobalTheory.HeckeScal.exists_scal_of_family | exact GlobalTheory.HeckeScal.exists_scal_of_family | (intros; apply GlobalTheory.HeckeScal.exists_scal_of_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaFunction_mixedCoordinate_bump_mul_core : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ) (g : WO S₀ T → ℂ), IsBump β → IsThetaFunO ψ S₀ T g → ∃ Φ, IsThetaFunO ψ S T Φ ∧ ∀ x, d.mixS T ψ v.μ v.𝓕 Φ x = β x • g := by
  first | exact @GlobalTheory.BumpMix.bump_mul_theta_mixS | exact GlobalTheory.BumpMix.bump_mul_theta_mixS | (intros; apply GlobalTheory.BumpMix.bump_mul_theta_mixS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumSourceLevelCharacterLawStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_sourceLevelCharacter_law : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → SourceLevelLawC R F := by
  first | exact @GlobalTheory.SourceLaw.sourceLevelLaw | exact GlobalTheory.SourceLaw.sourceLevelLaw | (intros; apply GlobalTheory.SourceLaw.sourceLevelLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLevelActionEqInvSmulTranslate
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups GlobalTheory.ThetaProjEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaCommutation

theorem exists_fin_part {D : D7} (V : HSp D) (q : Bridge.Gf V) : ∃ k ∈ GfC V, (finHom V).rangeRestrict k = q := by
  obtain ⟨h, rfl⟩ := (finHom V).rangeRestrict_surjective q
  obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
  refine ⟨k, hk, Subtype.ext ?_⟩
  show finHom V k = finHom V (a * k)
  rw [map_mul, show finHom V a = 1 from ha, one_mul]

theorem finiteGroupLevelAction_eq_inv_smul_translate {H W : Type} [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {Q : Subgroup H} (ch : Q →* ℂˣ)
    (q : Q) (k : H) (hk : k = q) (c : ℂ) (hc : c = ch q) (f : H → W) (h : H) :
    Bridge.g0Act ch q f h = c⁻¹ • f (h * k) := by
  rw [hk, hc, Bridge.g0Act, Units.val_inv_eq_inv_val]

theorem ch_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) :
    (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) := rfl

theorem exists_adelic_lift {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) (g0 : G0 L.Pg L.r) (hq : rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) = g0)
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] :
    ∃ k, IsLevelLift V β L g0 k ∧ ∀ (f : Bridge.Gf V → W) h,
      Bridge.g0Act (levEnv V β L).ch q f h = (levChi V β (flagL L) k)⁻¹ • f (h * (finHom V).rangeRestrict k) := by
  obtain ⟨k, hk, e⟩ := exists_fin_part V q.1
  have e1 : finE V k = Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _) :=
    congrArg (fun x : Bridge.Gf V => Formalism.UG.bc (swapAE D) x.1) e
  refine ⟨k, ⟨hk, ?_, ?_⟩, finiteGroupLevelAction_eq_inv_smul_translate _ q _ e _ ?_⟩
  · rw [e1]; exact q.2.1
  · rw [e1]; exact hq
  · exact congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans (ch_eq V β L q).symm)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem algW_apply (i : Fin D.R.m) (c : G → ℂ) (U : MMap (R.MW i (sg0 D A))) :
    algW R i c U = ∑ g, c g • FWT.actW R i (sg0 D A) g U := by
  refine MultilinearMap.ext fun v => ?_
  show (∑ g, c g • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) (U v) = _
  rw [LinearMap.sum_apply, _root_.sum_apply]
  rfl

theorem map_comb {G H X Y : Type} [Fintype G] [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (e : H →ₗ[ℂ] X) (he : Function.Injective e) (Θ : H →ₗ[ℂ] Y) (c : G → ℂ) (a : G → X) (b : G → Y) (y : H)
    (hy : e y = ∑ g, c g • a g) (h1 : ∀ g, ∃ z, e z = a g) (h2 : ∀ g z, e z = a g → Θ z = b g) :
    Θ y = ∑ g, c g • b g := by
  choose z hz using h1
  have h3 : y = ∑ g, c g • z g := he (by simp only [hy, map_sum, map_smul, hz])
  simp only [h3, map_sum, map_smul, h2 _ _ (hz _)]

end GlobalTheory.ThetaCommutation

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationOperatorMultiplierAntilinearStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCreationOperatorMultiplier_antilinear : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t : ℂ) a, GlobalTheory.FockTransl.Jet.lamF A B l (t • a) = conj t * GlobalTheory.FockTransl.Jet.lamF A B l a := by
  first | exact @GlobalTheory.FockTransl.Jet.lamF_antilinear | exact GlobalTheory.FockTransl.Jet.lamF_antilinear | (intros; apply GlobalTheory.FockTransl.Jet.lamF_antilinear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMatrixCoefficientEvenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuum_matrixCoefficient_even : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ (τ : D.what₂.Tau) YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → BS τ * YS * (BS τ)⁻¹ ∈ lieAt S τ ∧ BT τ * YT * (BT τ)⁻¹ ∈ lieAt T τ ∧ ∀ f g, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → IsThetaFunO ψ S T g → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) g) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ t : ℝ, ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f) g = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) g := by
  first | exact @GlobalTheory.VacuumEven.coeff_even | exact GlobalTheory.VacuumEven.coeff_even | (intros; apply GlobalTheory.VacuumEven.coeff_even <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijectionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_conjAdjointPullback_bijection : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (A : Fr S) (B : Fr T), ∃ j : PolF D T.rank S.rank ≃+ PolF D S.rank T.rank, (∀ (c : ℂ) P, j (c • P) = starRingEnd ℂ c • j P) ∧ ∀ f, IsVacF ψ θ A B f → IsVacF ψ θ B A (dag S T f) ∧ ∀ P, ptF ψ θ B A (dag S T f) (j P) = dag S T (ptF ψ θ A B f P) := by
  first | exact @GlobalTheory.FockAdjoint.fock_dag | exact GlobalTheory.FockAdjoint.fock_dag | (intros; apply GlobalTheory.FockAdjoint.fock_dag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsCompareByLevelMatchingEvaluationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodRows_compare_by_levelMatching_evaluation : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → RowLevelMatchAt R F X h t → ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd (iotaX X h).toMulEquiv t c' := by
  first | exact @GlobalTheory.SeeEval.evalTieT_of_levelMatch | exact GlobalTheory.SeeEval.evalTieT_of_levelMatch | (intros; apply GlobalTheory.SeeEval.evalTieT_of_levelMatch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodSplitPlaceOfFamilyPrimeBaseTupleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodSplitPlace_of_family_prime_base_tuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → ∀ P, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P ∧ A3.A.q P0 ≠ 0 := by
  first | exact @GlobalTheory.GoodSplitFam.good_split_pl | exact GlobalTheory.GoodSplitFam.good_split_pl | (intros; apply GlobalTheory.GoodSplitFam.good_split_pl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeEigenvaluesEqOfDualEnlargingLabelsSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEigenvalues_eq_of_dual_enlarging_labels_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (c c' : Pl D.host.E → List ℤ → ℂ), GlobalTheory.Hk3.EEc R SF c ≠ ⊥ → GlobalTheory.Hk3.EEc R SF c' ≠ ⊥ → (∀ P, GlobalTheory.Hk3.Good R A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k ≤ (Yc D 0).rank, c P (dualLab (splitLab (Yc D 0).rank k)) = c' P (dualLab (splitLab (Yc D 0).rank k))) → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ d, GlobalTheory.Hk3.IsLab (Yc D 0) P d → c P (dualLab d) = c' P (dualLab d) := by
  first | exact @GlobalTheory.Hk3.LabDetRows.dual_eq_of_split | exact GlobalTheory.Hk3.LabDetRows.dual_eq_of_split | (intros; apply GlobalTheory.Hk3.LabDetRows.dual_eq_of_split <;> assumption)
end

