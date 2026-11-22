import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def extJ (σ : L →+* ℂ) (jK : M →ₛₗ[σ.comp (algebraMap K L)] W) : L ⊗[K] M →ₛₗ[σ] W :=
  letI : Module K W := Module.compHom W (σ.comp (algebraMap K L))
  let B : L →ₗ[K] M →ₗ[K] W := LinearMap.mk₂ K (fun a m => σ a • jK m)
    (fun a a' m => by rw [map_add, add_smul])
    (fun k a m => by
      show σ (k • a) • jK m = (σ (algebraMap K L k)) • (σ a • jK m)
      rw [Algebra.smul_def, map_mul, mul_smul])
    (fun a m m' => by rw [map_add, smul_add])
    (fun k a m => by
      show σ a • jK (k • m) = (σ (algebraMap K L k)) • (σ a • jK m)
      rw [map_smulₛₗ, RingHom.comp_apply, smul_comm])
  { toFun := TensorProduct.lift B
    map_add' := map_add _
    map_smul' := fun a x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b m =>
        rw [TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        show σ (a • b) • jK m = σ a • (σ b • jK m)
        rw [smul_eq_mul, map_mul, mul_smul]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }

def incl : M →ₗ[K] L ⊗[K] M := TensorProduct.mk K L M 1

theorem incl_injective : Function.Injective (incl (K := K) (L := L) (M := M)) := by
  have h1 : Function.Injective ((Algebra.linearMap K L).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
  have h2 : (incl (K := K) (L := L) (M := M)) =
      ((Algebra.linearMap K L).rTensor M).comp (TensorProduct.lid K M).symm.toLinearMap := by
    ext m; simp [incl]
  rw [h2]
  exact h1.comp (TensorProduct.lid K M).symm.injective

end Ext

section Forms

variable {K : Type} [Field K] {LL : Type} [Field LL] [NumberField LL] [Algebra K LL]
variable {C : Type} [AddCommGroup C] [Module K C] {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {D : D7}

def rhoOf (LL : Type) [Field LL] [Algebra K LL] {G0 : Type} [Group G0] (ρC : G0 →* (C →ₗ[K] C)) :
    G0 →* (LL ⊗[K] C →ₗ[LL] LL ⊗[K] C) where
  toFun g := (ρC g).baseChange LL
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g g' := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

def formsLOf (Comp : (LL →+* ℂ) → Type) (X : ∀ σ, Comp σ → Data E r) (la : ∀ σ c, Wt (X σ c).Ψ r)
    (rd : ∀ σ : LL →+* ℂ, C →ₛₗ[σ.comp (algebraMap K LL)] FDSec (X σ)) (V : (LL →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame (X σ k).Ψ r) (mu : ∀ σ, GA D (V σ) → ℂ)
    (hL2 : ∀ σ, JMemL2 (V σ) (σ.comp (algebraMap K LL)) (rd σ) (dict σ) (mu σ))
    (hRd : ∀ σ, RdHolCusp (σ.comp (algebraMap K LL)) (la σ) (rd σ))
    [NumberField K] (Pt : HeightOneSpectrum (𝓞 K) → Type) (nrmC : ∀ lp, Pt lp → C → ℝ)
    (h0 : ∀ lp y f, 0 ≤ nrmC lp y f) (hz : ∀ lp y, nrmC lp y 0 = 0)
    (ha : ∀ lp y f g, nrmC lp y (f + g) ≤ max (nrmC lp y f) (nrmC lp y g))
    (hs : ∀ lp y (x : K) f, nrmC lp y (x • f) = FinitePlace.mk lp x * nrmC lp y f)
    {G0 : Type} [Group G0] (ρC : G0 →* (C →ₗ[K] C)) (chiC : G0 →* Kˣ) :
    Formalism.IndefR.Arith.FormsL LL K (LL ⊗[K] C) (fun σ => ↥(SS (V σ) (la σ) (dict σ) (mu σ))) G0 where
  WK := LinearMap.range (incl (K := K) (L := LL) (M := C))
  Pt := Pt
  nrm lp y w := nrmC lp y ((LinearEquiv.ofInjective _ incl_injective).symm w)
  nrm_nonneg lp y w := h0 lp y _
  nrm_zero lp y := by rw [map_zero]; exact hz lp y
  nrm_add lp y w w' := by rw [map_add]; exact ha lp y _ _
  nrm_smul lp y x w := by rw [map_smul]; exact hs lp y x _
  towKs := inferInstance
  ρ := rhoOf LL ρC
  chi := (Units.map (algebraMap K LL).toMonoidHom).comp chiC
  j σ := extJ σ (jSS (V σ) (σ.comp (algebraMap K LL)) (la σ) (rd σ) (dict σ) (mu σ) (hL2 σ) (hRd σ))

def mapX {WL : Type} [AddCommGroup WL] [Module LL WL] [Module K WL] [NumberField K]
    {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] {G0 : Type} [Group G0]
    (A : Formalism.IndefR.Arith.FormsL LL K WL W G0) (u : ∀ σ, W σ ≃ₗ[ℂ] W' σ) :
    Formalism.IndefR.Arith.FormsL LL K WL W' G0 :=
  { A with j := fun σ => (u σ).toLinearMap.comp (A.j σ) }

def BaseEmbeddingInclusion (F : IntermediateField ℚ ℂ) [Algebra F LL] (σ₀ : LL →+* ℂ) : Prop :=
  ∀ x : F, σ₀ (algebraMap F LL x) = (x : ℂ)

end Forms

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LandherrSelfDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (D₁ D₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), D₁.p = D₂.p → D₁.q = D₂.q →
    ∃ (N : ℕ) (f : D₁.La →ₗ[𝓞 E] D₂.La), 0 < N ∧ Function.Injective f ∧
      ∀ x y, D₂.EF (f x) (f y) = (N : ℤ) ^ 2 * D₁.EF x y

variable {D : D7}

section Model

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

end Model

end Formalism.L2.Pj

end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ExistsParPinsOfRec
section
namespace Formalism.L2.Pj

open Formalism.BasicNotions

theorem exists_par_pins_of_rec (D : D7) (hF : OFull D) (hz : OZeta D) (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.N1ab) :
    ∃ Q : Par D, Q.Pins :=
  exists_parameter_conditions D hF hz (fun j hj => ⟨datInt_of Formalism.IndefR.Fin.factPrincipalDatum D j,
    ⟨efW_unimod_of Formalism.IndefR.Fin.factPrincipalDatum D j _, latW_rank D j hj, datDom_holds D j hj _⟩⟩) hN

end Formalism.L2.Pj
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def lamOf (la : HeightOneSpectrum (𝓞 c.F)) : PointsOfFlagModel.abelian₂ (Formalism.MainNotions.WeightAlgebra.resCh la) c :=
  ⟨la, by
    have h : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : 𝓞 c.F ⧸ la.asIdeal) = 0 := by
      unfold Formalism.MainNotions.WeightAlgebra.resCh
      exact CharP.cast_eq_zero _ _
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (by simpa using h)⟩

def LiesOverBaseChange (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (η : PointsOfFlagModel.Pt Tw .yy) : Prop :=
  letI := io.toAlgebra
  η.1 = lamOf la ∧ ∃ eF : T.Fr →+* ↥η.2.1.S,
    eF.comp io = η.2.2.1.fK ∧
    (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧
    (∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧
    η.2.2.1.y ≫ pullback.fst _ _ = spMap eF ≫ y.1.x ∧
    ∀ τ i, ∃ u' : Sp (DualNumber ↥η.2.1.S) ⟶ (Tw.Y η.1).oF.t.G.left,
      u' ≫ (Tw.Y η.1).m.φ = (η.2.2.2.u τ i).left ∧
      u' ≫ (Tw.Y η.1).m0.toSABMap.φ = spMap (dualMap eF) ≫ y.1.u τ i

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  sec Xo c a n ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laU (U σ) a n)).comap (rdU (U σ))

theorem cusp_le_sec (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n ≤ sec Xo c a n := inf_le_left

theorem mem_cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    f ∈ cusp Xo c U a n ↔ f ∈ sec Xo c a n ∧ ∀ σ : c.F →+* ℂ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (laU (U σ) a n) := by
  unfold cusp
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]

def mulC (f g : Rul Xo c) : Rul Xo c := f * g

theorem mulC_mem_sec (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) {f g : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (hg : g ∈ sec Xo c a' n') : mulC Xo c f g ∈ sec Xo c (a + a') (n + n') := by
  unfold mulC
  exact sec_mul Xo c a a' n n' hf hg

def CuspMul : Prop :=
  ∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), Dom a n → Dom a' n' → f ∈ cusp Xo c U a n →
    g ∈ cusp Xo c U a' n' → mulC Xo c f g ∈ cusp Xo c U (a + a') (n + n')

def CuspFD : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)

def algCls (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι) : Prop := y.IsAlg

def valSet (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) :=
  Set.range (vAtV : PtV Xo c cls Unit (fun _ _ _ _ => True) la → Rul Xo c → EReal)

variable {Xo c cls}

theorem isVal_vAt {PY : Type} {lies : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) : IsVal la (vAtV y) :=
  ⟨vAtV_zero y, vAtV_ne_bot y, vAtV_add y, fun a f ha => vAtV_smul y a f ha, vAtV_mul y⟩

theorem isVal_valSet (la : HeightOneSpectrum (𝓞 c.F)) : ∀ v ∈ valSet Xo c cls la, IsVal la v := by
  rintro _ ⟨y, rfl⟩
  exact isVal_vAt y

variable (Xo c cls)

def LiesTotal (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ la (T : CDVR) (ι : c.F →+* T.Fr) (e : ℕ), OverLa la T.V ι e → ∀ y : IntFr Xo c T ι, cls T ι y →
    ∃ η, lies la T ι y η

variable {Xo c cls}

theorem nonneg_iff_of_liesTotal {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (h : LiesTotal Xo c cls PY lies) (f : Rul Xo c) :
    (∀ la, ∀ v ∈ valSet Xo c cls la, 0 ≤ v f) ↔
      ∀ la (y : PtV Xo c cls (PY la) (lies la) la), 0 ≤ vAtV y f := by
  constructor
  · rintro h0 la ⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩
    exact h0 la _ ⟨PtV.mk la ho y hy () trivial, rfl⟩
  · rintro h0 la _ ⟨⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
    obtain ⟨η', hη'⟩ := h la T ι e ho y hy
    exact h0 la (PtV.mk la ho y hy η' hη')

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Calc

variable {X X' Y : Scheme.{0}}

def thfPull (L : LB X) (F : X' ⟶ X) (s : LB.Sec L) : LB.Sec (L.pull F) where
  f := fun (J : PUnit → L.ι) =>
    (F.appLE (L.U (J PUnit.unit)) ((L.pull F).U J) (LB.wchart_le L _ J PUnit.unit)).hom (s.f (J PUnit.unit))
  compat := fun (J J' : PUnit → L.ι) => fn_ext fun y hy => by
    have h₁ : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.1
    have h₂ : F y ∈ L.U (J' PUnit.unit) := mem_pull.1 hy.2
    exact (gs_res _ y _ hy _).trans ((gs_appLE F _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 X' ≫ F) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val (gm_pull_g L F (𝟙 _) y J J' hy.1 hy.2)))
        ((gs_res _ y _ hy _).trans (gs_appLE F _ _ _ (𝟙 _) y hy.2 _)))))))

theorem thfPull_f (L : LB X) (F : X' ⟶ X) (s : LB.Sec L) (J : PUnit → L.ι) :
    (thfPull L F s).f J =
      (F.appLE (L.U (J PUnit.unit)) ((L.pull F).U J) (LB.wchart_le L _ J PUnit.unit)).hom (s.f (J PUnit.unit)) := rfl

theorem chart_le_pullback_open (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ h ⁻¹ᵁ (L.pull F).U (fun _ => j 0) := by
  intro y hy
  have h0 := LB.wchart_le L (fun _ : Fin 1 => φ) j 0 hy
  show h y ∈ (L.pull F).U (fun _ => j 0)
  rw [mem_pull]
  subst e
  simpa using h0

def thfPull1 (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (s : LB.Sec (L.pull F)) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)) where
  f := fun (j : Fin 1 → L.ι) => (h.appLE _ _ (chart_le_pullback_open L h e j)).hom (s.f (fun _ => j 0))
  compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
    have h₁ : h y ∈ (L.pull F).U (fun _ => j 0) := chart_le_pullback_open L h e j hy.1
    have h₂ : h y ∈ (L.pull F).U (fun _ => j' 0) := chart_le_pullback_open L h e j' hy.2
    have g : gm (𝟙 Y) y _ ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).g j j') =
        gm (𝟙 Y ≫ φ) y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) :=
      (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2).trans (by rw [Fin.prod_univ_one, zpow_one])
    have eφ : (𝟙 Y ≫ h) ≫ F = 𝟙 Y ≫ φ := by rw [Category.assoc, e]
    exact (gs_res _ y _ hy _).trans ((gs_appLE h _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 Y ≫ h) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val (g.trans ((congrArg (fun q => gm q y (L.U (j 0) ⊓ L.U (j' 0))
          (L.g (j 0) (j' 0))) eφ).symm.trans (gm_pull_g L F (𝟙 Y ≫ h) y _ _ h₁ h₂).symm))))
        ((gs_res _ y _ hy _).trans (gs_appLE h _ _ _ (𝟙 _) y hy.2 _)))))))

theorem thf_secUp {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB)
    (hL' : L'.IsLB) (σ : LB.Sec L') : ∃ s : LB.Sec (L.pull F), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z)
      (J : PUnit → L.ι) (k : L'.ι), r z ∈ (L.pull F).U J → r z ∈ L'.U k →
      gs r z _ (s.f J) = (gw w r z (J PUnit.unit) k).val * gs r z _ (σ.f k) := by
  have hP : ∀ K : PUnit → L'.ι, (L'.pull (𝟙 X')).U K ≤ L'.U (K PUnit.unit) := fun K x hx => by
    have hx' := (mem_pull (L := L') (F := 𝟙 X')).1 hx
    simpa using hx'
  obtain ⟨w', hw'⟩ : ∃ w' : LB.Iso (L.pull F) (L'.pull (𝟙 X')), ∀ (Y : Scheme.{0}) (f : Y ⟶ X') (y : Y) (j : L'.ι)
      (K : PUnit → L.ι), f y ∈ L'.U j → f y ∈ (L.pull F).U K → gw w' f y j K = (gw w f y (K PUnit.unit) j)⁻¹ := by
    refine ⟨⟨fun p => (res (le_inf inf_le_right (inf_le_left.trans (hP p.1))) (w.s (p.2, p.1 PUnit.unit)))⁻¹⟩, ?_⟩
    intro Y f y j K hj hK
    have hm : f y ∈ (L'.pull (𝟙 X')).U (fun _ => j) ⊓ (L.pull F).U K :=
      ⟨(mem_pull (L := L') (F := 𝟙 X')).2 (by simpa using hj), hK⟩
    unfold gw
    dsimp only
    exact (map_inv (gm f y _) _).trans (congrArg (·⁻¹) (gm_res f y _ hm _))
  have hPG : PGen w' := by
    intro Y f y j j' k k' hj hj' hk hk'
    have hj0 : f y ∈ L'.U j := by simpa using hj
    have hj0' : f y ∈ L'.U j' := by simpa using hj'
    rw [hw' Y f y j k hj0 hk, hw' Y f y j' k' hj0' hk', gm_pull_g L F f y k k' hk hk', Category.comp_id,
      hw Y f y (k PUnit.unit) (k' PUnit.unit) j j' (mem_pull.1 hk) (mem_pull.1 hk') hj0 hj0']
    simp only [mul_inv, inv_inv]
    ac_rfl
  obtain ⟨s, hs⟩ := sec_down (L := L') (F := 𝟙 X') (L' := L.pull F) (w := w') hPG hL' (pull_isLB hL F)
    (fun j => (Scheme.Hom.appLE (𝟙 X') (L'.U j) ((𝟙 X') ⁻¹ᵁ L'.U j) le_rfl).hom (σ.f j)) (by
      intro y j j' hj hj'
      rw [gs_appLE (𝟙 X') (L'.U j) ((𝟙 X') ⁻¹ᵁ L'.U j) le_rfl (𝟙 X') y hj,
        gs_appLE (𝟙 X') (L'.U j') ((𝟙 X') ⁻¹ᵁ L'.U j') le_rfl (𝟙 X') y hj', Category.comp_id]
      exact gs_compat σ (𝟙 X') y hj hj')
  refine ⟨s, fun Z r z J k hJ hk => ?_⟩
  have hk1 : (𝟙 X') (r z) ∈ L'.U k := by simpa using hk
  have e := hs Z r z k J hk1 hJ
  rw [gs_appLE (𝟙 X') (L'.U k) ((𝟙 X') ⁻¹ᵁ L'.U k) le_rfl r z hk, Category.comp_id, hw' Z r z k J hk hJ] at e
  rw [e, ← _root_.mul_assoc, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, _root_.one_mul]

end Calc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

set_option maxHeartbeats 400000 in

theorem thetaFrame_of (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) : ThetaFrameSt Xo c := by
  intro T io O _ β Y hPI yt z hz hzs G m t' m1 m2
  obtain ⟨θ, hθ, -, w2, σ', ⟨g2, r2⟩, hcl, hgen⟩ := thetaCore_of hT E H Dw l Xo c O β Y hPI T.V yt z hz G m t' m2
  generalize (z ≫ pullback.fst _ _ : Sp T.Fr ⟶ Xo.X) = x at m1 ⊢
  intro s₀ hs₀
  obtain ⟨w1, g1, r1, -⟩ := m1.lin
  have hw1 := (isGen_iff w1).1 g1
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨s1, hs1⟩ := thf_secUp hw1 hL hL' σ'
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ t'.G.left := m1.cart.1.lift _ _ cond
  have hφ : h ≫ m1.φ = (snd (Over.mk x) A).left := m1.cart.1.lift_fst _ _ cond
  have hh : h ≫ t'.G.hom = (fst (Over.mk x) A).left := m1.cart.1.lift_snd _ _ cond
  let a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t'.G.hom rfl
  let b0 : Over.mk (t'.G.hom ≫ x) ⟶ A := Over.homMk m1.φ m1.cart.1.w
  let g0 : t'.G.left ⟶ Gx x := (lift a0 b0).left
  have g0f : g0 ≫ (fst (Over.mk x) A).left = t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
  have g0s : g0 ≫ (snd (Over.mk x) A).left = m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
  have uniq : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m1.φ → g ≫ (fst (Over.mk x) A).left = t'.G.hom →
      g ≫ h = 𝟙 _ := fun g e₁ e₂ => m1.cart.1.hom_ext (by rw [Category.assoc, hφ, e₁, Category.id_comp])
        (by rw [Category.assoc, hh, e₂, Category.id_comp])
  have hg0 : g0 ≫ h = 𝟙 _ := uniq g0 g0s g0f
  have h0g : h ≫ g0 = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      show h ≫ g0 ≫ (fst (Over.mk x) A).left = 𝟙 _ ≫ (fst (Over.mk x) A).left
      rw [g0f, hh, Category.id_comp]
    · rw [Category.assoc]
      show h ≫ g0 ≫ (snd (Over.mk x) A).left = 𝟙 _ ≫ (snd (Over.mk x) A).left
      rw [g0s, hφ, Category.id_comp]
  let s : LB.Sec (PPx x) := thfPull1 Xo.univ.t.PP.L h hφ s1
  have hsf : ∀ j : Fin 1 → Xo.univ.t.PP.L.ι, s.f j = (h.appLE _ _ (chart_le_pullback_open _ h hφ j)).hom (s1.f (fun _ => j 0)) :=
    fun j => rfl
  let θ2 := thfPull G.PP.L m2.φ θ
  have hI2 : IsoMaps w2 σ' θ2 := fun (i : PUnit → G.PP.L.ι) k => fn_ext fun y hy => by
    have h₁ : (G.PP.L.pull m2.φ).U i ⊓ t'.PP.L.U k ≤ m2.φ ⁻¹ᵁ G.PP.L.U (i PUnit.unit) :=
      inf_le_left.trans (LB.wchart_le G.PP.L _ i PUnit.unit)
    have h₂ : (G.PP.L.pull m2.φ).U i ⊓ t'.PP.L.U k ≤ (G.PP.L.pull m2.φ).U (fun _ => i PUnit.unit) ⊓ t'.PP.L.U k :=
      le_rfl
    have e := congrArg (gs (𝟙 _) y _) (hcl (i PUnit.unit) k _ h₁ h₂)
    refine (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans
      (((gs_appLE m2.φ _ _ h₁ (𝟙 _) y hy _).symm.trans e).trans ((gs_mul _ y _ hy _ _).trans ?_)))
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_res _ y h₂ hy _).symm ((gs_res _ y _ hy _).trans (gs_res _ y _ hy _).symm)
  have hI1 : IsoMaps w1 σ' s1 := fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun y hy => by
    exact (gs_res _ y _ hy _).trans ((hs1 _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  have hgc : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m1.φ → g ≫ (fst (Over.mk x) A).left = t'.G.hom →
      ∀ (j : PUnit → Xo.univ.t.PP.L.ι) (hj : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
        s1.f j = (g.appLE _ _ hj).hom (s.f (fun _ => j PUnit.unit)) := fun g e₁ e₂ j hj => fn_ext fun y hy =>
    Eq.symm ((gs_appLE g _ _ hj (𝟙 _) y hy _).trans
      ((gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g) y (hj hy) _).trans
        (congrArg (fun q => gs q y _ (s1.f j)) (by rw [Category.id_comp, uniq g e₁ e₂]))))
  have hgenS : ∀ s'' : LB.Sec (PPx x), ∃! a : T.Fr, ∀ i, s''.f i = scal x a i * s.f i := by
    intro s''
    have le : ∀ j, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ g0 ⁻¹ᵁ (PPx x).U (fun _ => j) := fun j y hy =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) g0s).mpr hy
    let σ : ∀ j, Γ(t'.G.left, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j) := fun j => (g0.appLE _ _ (le j)).hom (s''.f (fun _ => j))
    have gP : ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z) j, m1.φ (r z) ∈ Xo.univ.t.PP.L.U j →
        gs r z _ (σ j) = gs (r ≫ g0) z _ (s''.f (fun _ => j)) := fun Z r z j hz => gs_appLE g0 _ _ (le j) r z hz _
    obtain ⟨τ, hτ⟩ := sec_down hw1 hL hL' σ fun y j j' h₁ h₂ => by
      have m : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j) := le j h₁
      have m' : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j') := le j' h₂
      have gg : gm (𝟙 _ ≫ g0) y _ ((PPx x).g (fun _ => j) (fun _ => j')) =
          gm m1.φ y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j') :=
        (gm_linComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (snd (Over.mk x) A).left) (fun _ => 1) (𝟙 _ ≫ g0) y _ _ m m').trans
          (by rw [Fin.prod_univ_one, zpow_one, Category.assoc, g0s, Category.id_comp])
      exact (gP _ (𝟙 _) y j h₁).trans ((gs_compat s'' (𝟙 _ ≫ g0) y m m').trans
        (congrArg₂ (· * ·) (congrArg Units.val gg) (gP _ (𝟙 _) y j' h₂).symm))
    obtain ⟨a, ha, hu⟩ := hgen τ
    refine ⟨a, fun (i : Fin 1 → Xo.univ.t.PP.L.ι) => ?_, fun a' ha' => hu a' ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
      refine fn_ext fun y hy => ?_
      have mφ : m1.φ ((𝟙 _ ≫ h) y) ∈ Xo.univ.t.PP.L.U j :=
        (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j)
          (by rw [Category.id_comp, hφ] : (𝟙 _ ≫ h) ≫ m1.φ = (snd (Over.mk x) A).left)).mpr (Set.mem_iInter.1 hy 0)
      obtain ⟨k, hk⟩ := exists_chart hL' ((𝟙 _ ≫ h) y)
      have e1 : gs (𝟙 _) y _ (s''.f (fun _ => j)) =
          (gw w1 (𝟙 _ ≫ h) y j k).val * (cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a * gs (𝟙 _ ≫ h) y _ (σ'.f k)) := by
        have c1 : (𝟙 _ ≫ h) ≫ g0 = 𝟙 _ := by rw [Category.id_comp, h0g]
        refine (congrArg (fun q => gs q y _ (s''.f (fun _ => j))) c1).symm.trans ?_
        refine (gP _ (𝟙 _ ≫ h) y j mφ).symm.trans ((hτ _ (𝟙 _ ≫ h) y j k mφ hk).trans (congrArg _ ?_))
        rw [ha k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]
      have e2 : gs (𝟙 _) y _ (s.f (fun _ => j)) = (gw w1 (𝟙 _ ≫ h) y j k).val * gs (𝟙 _ ≫ h) y _ (σ'.f k) :=
        (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _) y hy _).trans
          (hs1 _ (𝟙 _ ≫ h) y (fun _ => j) k (chart_le_pullback_open _ h hφ _ hy) hk)
      have e3 : gs (𝟙 _) y _ (scal x a (fun _ => j)) = cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a := by
        rw [show (𝟙 _ ≫ h) ≫ t'.G.hom = 𝟙 _ ≫ (fst (Over.mk x) A).left by rw [Category.assoc, hh]]
        exact gs_constFn (fst (Over.mk x) A).left _ (𝟙 _) y hy a
      exact e1.trans ((mul_left_comm _ _ _).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e3 e2))))
    · intro k
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ := exists_chart hL (m1.φ y)
      have c2 : (𝟙 _ ≫ g0) ≫ h = 𝟙 _ := by rw [Category.id_comp, hg0]
      have mg : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j) := le j hj
      have e1 := hτ _ (𝟙 _) y j k hj hy
      have e2 : gs (𝟙 _) y _ (σ j) =
          cst (𝟙 _ ≫ t'.G.hom) y a' * ((gw w1 (𝟙 _) y j k).val * gs (𝟙 _) y _ (σ'.f k)) := by
        refine (gP _ (𝟙 _) y j hj).trans ?_
        rw [ha' (fun _ => j), gs_mul _ y _ mg]
        refine congrArg₂ (· * ·) ?_ ?_
        · exact (gs_constFn (fst (Over.mk x) A).left _ _ y mg a').trans (by rw [Category.assoc, g0f])
        · refine (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g0) y mg _).trans ?_
          rw [c2]
          exact hs1 _ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hy
      rw [gs_mul _ y _ hy, gs_constFn _ _ _ y hy]
      rw [e1, mul_left_comm] at e2
      exact (Units.mul_right_inj _).1 e2
  obtain ⟨a, ha, -⟩ := hs₀ s
  have a0 : a ≠ 0 := by
    rintro rfl
    have z0 : ∀ i, s.f i = 0 := fun i => by
      rw [ha i]
      simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, toΓ, map_zero, zero_mul]
    obtain ⟨b, -, hb⟩ := hgenS s
    exact zero_ne_one ((hb 0 fun i => by rw [z0 i, mul_zero]).trans (hb 1 fun i => by rw [z0 i, mul_zero]).symm)
  exact ⟨θ, s, hθ, ⟨w1, w2, σ', s1, θ2, ⟨g1, r1⟩, ⟨g2, r2⟩, hI1, hI2, fun j hj => rfl, hgc⟩, hgenS,
    Units.mk0 a a0, ha⟩

end Formalism.L2.Pj
end
end

