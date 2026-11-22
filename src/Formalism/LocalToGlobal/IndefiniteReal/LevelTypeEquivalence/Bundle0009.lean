import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FDMSubCompact
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContReal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem clm_sum {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] (ℓ : (Fin k → ℝ) →L[ℝ] M) (s : Fin k → ℝ) :
    ℓ s = ∑ i, s i • ℓ (ev i) := by
  have : s = ∑ i, s i • ev i := by
    funext j; simp [ev, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  rw [map_sum]
  simp [map_smul]

section Real

variable (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T) (hL : Continuous L)

include hΛ hL in

theorem beta_poly (s t : Fin k → ℝ) :
    Λ (symplOH S T (L s) (L t)).1 = ∑ i, ∑ j, s i * t j * Λ (symplOH S T (L (ev i)) (L (ev j))).1 := by

  have hs : ∀ t, Λ (symplOH S T (L s) (L t)).1 = ∑ i, s i * Λ (symplOH S T (L (ev i)) (L t)).1 := by
    intro t
    let g : (Fin k → ℝ) →+ ℂ := AddMonoidHom.mk' (fun s => Λ (symplOH S T (L s) (L t)).1) (fun a b => by
      simp only [map_add, symplOH_add_left]; exact Λ.map_add _ _)
    have hg : Continuous g := by
      have h1 : Continuous fun s => symplOH S T (L s) (L t) := (continuous_symplOH_left (L t)).comp hL
      exact hΛ.comp (continuous_fst.comp h1)
    have := clm_sum (AddMonoidHom.toRealLinearMap g hg) s
    simpa [g, smul_eq_mul] using this
  rw [hs t]
  refine Finset.sum_congr rfl fun i _ => ?_
  let g : (Fin k → ℝ) →+ ℂ := AddMonoidHom.mk' (fun t => Λ (symplOH S T (L (ev i)) (L t)).1) (fun a b => by
    simp only [map_add, symplOH_add_right]; exact Λ.map_add _ _)
  have hg : Continuous g := by
    have h1 : Continuous fun t => symplOH S T (L (ev i)) (L t) := (continuous_symplOH_right _).comp hL
    exact hΛ.comp (continuous_fst.comp h1)
  have := clm_sum (AddMonoidHom.toRealLinearMap g hg) t
  simp only [AddMonoidHom.coe_toRealLinearMap, g, AddMonoidHom.mk'_apply, smul_eq_mul] at this
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.real_smul]
  ring

end Real

section RealCont

variable {ψ : AddChar (AF D.host.F) ℂ} {Λ : Ainf D.host.F →+ ℂ} (hΛ : Continuous Λ)
  (hψΛ : ∀ z : AF D.host.F, z.2 = 0 → ψ z = Complex.exp (Λ z.1))
  {L : (Fin k → ℝ) →+ WO S T} (hL : IsRealFrame L)

include hΛ hψΛ hL in

theorem cont_real {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x0 : WO S T) {n : ℕ} (l : Fin n → Fin k) :
    Continuous fun s => dH ψ L l f (x0 + L s) := by
  set b : Fin k → Fin k → ℂ := fun i j => Λ (symplOH S T (L (ev i)) (L (ev j))).1
  set g0 : (Fin k → ℝ) → ℂ := fun r => f (x0 + L r)
  have hg0 : ContDiff ℝ ∞ g0 := hf.smooth k L hL.1 hL.2.1 x0
  set ℓ := ellx Λ hΛ L hL.1 x0
  set Φ : (Fin k → ℝ) × (Fin k → ℝ) → ℂ := fun p =>
    Complex.exp (ℓ p.2 + ∑ i, ∑ j, (p.1 i : ℂ) * (p.2 j : ℂ) * b i j) * g0 (p.1 + p.2)
  have hΦ : ContDiff ℝ ∞ Φ := by
    have h1 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × (Fin k → ℝ) => ℓ p.2 := ℓ.contDiff.comp contDiff_snd
    have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × (Fin k → ℝ) => ∑ i, ∑ j, (p.1 i : ℂ) * (p.2 j : ℂ) * b i j := by
      refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
      refine ContDiff.mul (ContDiff.mul ?_ ?_) contDiff_const
      · exact Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ i).comp contDiff_fst)
      · exact Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ j).comp contDiff_snd)
    exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp (h1.add h2)).mul (hg0.comp (contDiff_fst.add contDiff_snd))
  have hGf : ∀ s, Gf ψ L f (x0 + L s) = fun t => Φ (s, t) := by
    intro s; funext t
    have hrs : eInf D • L s = L s := (wo_real_iff (L s)).mp (hL.2.1 s)
    have hrt : eInf D • L t = L t := (wo_real_iff (L t)).mp (hL.2.1 t)
    simp only [Gf, heisO, Φ, g0]
    rw [symplOH_add_left]
    have h2 : (symplOH S T x0 (L t) + symplOH S T (L s) (L t)).2 = 0 := by
      show (symplOH S T x0 (L t)).2 + (symplOH S T (L s) (L t)).2 = 0
      rw [symplOH_snd _ _ hrt, symplOH_snd _ _ hrt, add_zero]
    rw [hψΛ _ h2, show (symplOH S T x0 (L t) + symplOH S T (L s) (L t)).1 =
      (symplOH S T x0 (L t)).1 + (symplOH S T (L s) (L t)).1 from rfl, map_add, beta_poly Λ hΛ L hL.1 s t,
      map_add, add_assoc]
    rfl
  have hval : ∀ s, dH ψ L l f (x0 + L s) = iteratedFDeriv ℝ n Φ (s, 0) (fun i => (0, ev (l i))) := by
    intro s
    have e : dH ψ L l f (x0 + L s) = iteratedFDeriv ℝ n (Gf ψ L f (x0 + L s)) 0 (fun i => ev (l i)) := rfl
    rw [e, hGf s]
    have hcomp : (fun t => Φ (s, t)) = (fun q => Φ (q + (s, 0))) ∘ (ContinuousLinearMap.inr ℝ (Fin k → ℝ) (Fin k → ℝ)) := by
      funext t; simp
    have hΦs : ContDiff ℝ ∞ (fun q => Φ (q + (s, 0))) := hΦ.comp (contDiff_id.add contDiff_const)
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.inr ℝ (Fin k → ℝ) (Fin k → ℝ))
      hΦs 0 (natCast_lt_inf n).le, iteratedFDeriv_comp_add_right]
    simp
  simp_rw [hval]
  exact (ContinuousMultilinearMap.apply ℝ _ ℂ _).continuous.comp
    ((hΦ.continuous_iteratedFDeriv (natCast_lt_inf n).le).comp (continuous_id.prodMk continuous_const))

end RealCont

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasBrg
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def uM (x : (UI.instV fr).GA) (v : InfinitePlace D.host.F) : Matrix (Fin V.rank) (Fin V.rank) ℂ := uMat (x.1 v)

theorem thetaV_eq_psiT (ρ : D.what₂.Tau) :
    Formalism.L2.SG.AdBridge.thetaV (UI.instV fr) (Formalism.L2.Host.tauPl D ρ) = psiT D ρ := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x =>
    have h1 := Formalism.L2.SG.AdBridge.thetaV_tmul (UI.instV fr) (Formalism.L2.Host.tauPl D ρ) a x
    have h2 : ∀ (a : AF D.host.F) (x : D.host.E),
        psiT D ρ (a ⊗ₜ[D.host.F] x) = gW D (plW D ρ) (fstA D.host.F a) * tauE D ρ x := fun a x => by
      show thetaC D ρ ((fstA D.host.F a) ⊗ₜ[D.host.F] x) = _
      rw [thetaC_tmul]
    refine h1.trans (Eq.trans ?_ (h2 a x).symm)
    have h3 : tauE D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D ρ)) x = tauE D ρ x := by
      rw [Equiv.symm_apply_apply]
    exact congrArg₂ (· * ·) rfl h3
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem P_isUnit_det (v : InfinitePlace D.host.F) : IsUnit (fr.P v).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (fr.unit v)

theorem infMat_brg (x : (UI.instV fr).GA) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (thetaC D ρ) (UI.brg fr x) =
      fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
  have hb : uM fr x (Formalism.L2.Host.tauPl D ρ) = (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ *
      (matA D V (UI.brg fr x)).map (psiT D ρ) * fr.P (Formalism.L2.Host.tauPl D ρ) := by
    have h := ((UI.brg_isBridge fr) x).1 (Formalism.L2.Host.tauPl D ρ)
    have h2 := thetaV_eq_psiT fr ρ
    unfold Formalism.L2.SG.AdBridge.ofHAInf at h
    rw [h2] at h
    exact h
  rw [hb, infMat_thetaC]
  have hu := P_isUnit_det fr (Formalism.L2.Host.tauPl D ρ)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem mat_eq_one_of_thetaC {M : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ ρ, M.map (thetaC D ρ) = 1) : M = 1 := by
  ext i j
  have hz : M i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j = 0 := by
    apply thetaC_inj
    intro ρ
    have := congrFun (congrFun (h ρ) i) j
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact sub_eq_zero.mp hz

theorem uM_one_iff (x : (UI.instV fr).GA) : x.1 = 1 ↔ ∀ v, uM fr x v = 1 := by
  unfold uM uMat
  constructor
  · rintro h v
    rw [h]
    rfl
  · intro h
    funext v
    exact Subtype.ext (Units.ext (h v))

theorem brg_mem_GfC (x : (UI.instV fr).GA) : UI.brg fr x ∈ GfC V ↔ x.1 = 1 := by
  have key : UI.brg fr x ∈ GfC V ↔ (matA D V (UI.brg fr x)).map (infPart D) = 1 := by
    constructor
    · intro hh
      exact congrArg (fun u : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1) (MonoidHom.mem_ker.mp hh)
    · intro hh
      exact MonoidHom.mem_ker.mpr (Units.ext hh)
  rw [key, uM_one_iff]
  have hc : ∀ ρ, ((matA D V (UI.brg fr x)).map (infPart D)).map (thetaC D ρ) =
      fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
    intro ρ
    rw [← infMat_brg, infMat_thetaC, Matrix.map_map]
    rfl
  constructor
  · intro h1 v
    obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
    have hu := P_isUnit_det fr (Formalism.L2.Host.tauPl D ρ)
    have e' : fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ = 1 := by
      rw [← hc ρ, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc uM fr x (Formalism.L2.Host.tauPl D ρ)
        = (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ * (fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) *
          (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹) * fr.P (Formalism.L2.Host.tauPl D ρ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
      _ = 1 := by rw [e', Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  · intro h1
    apply mat_eq_one_of_thetaC
    intro ρ
    rw [hc ρ, h1, Matrix.mul_one, Matrix.mul_nonsing_inv _ (P_isUnit_det fr _)]

theorem tauF_eq : Formalism.L2.SG.AdBridge.tauF (UI.instV fr) =
    (Lev.swapAE D).comp (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x => exact (Formalism.L2.SG.AdBridge.tauF_tmul (UI.instV fr) a x).trans rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem finE_brg (x : (UI.instV fr).GA) : Lev.finE V (UI.brg fr x) = (x.2.1 : GL (Fin V.rank) (Lev.EAf D)) := by
  apply Units.ext
  have hb := ((UI.brg_isBridge fr) x).2
  unfold Formalism.L2.SG.AdBridge.ofHAFin at hb
  rw [tauF_eq] at hb
  exact hb.symm

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.PrincipalLevelAction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def principalLevelAction (g : G) : (GA D (Yc D 0) → ℂ) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) := actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)

def actYt (t : T) (j : ℕ) (g : G) : (GA D (Yc D j) → ℂ) →ₗ[ℂ] (GA D (Yc D j) → ℂ) :=
  actL (Yc D j) (R.βY j) (R.datYt t j R.triv) (R.eG g)

def actX (t : T) (g : G) : (GA D D.sp.X' → ℂ) →ₗ[ℂ] (GA D D.sp.X' → ℂ) := actL D.sp.X' R.βX (R.datXt t) (R.eG g)

def actW (i : Fin D.R.m) (g : G) : (GA D (Wc D i) → ℂ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
  actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)

def fX (t : T) : (R.HX t).H →ₗ[ℂ] (SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) := R.cX.toMap R.prX ∘ₗ (R.HX t).e

def GUnitC : Prop := ∀ (g : G) (x y : R.HE.H), inner ℂ (R.gE g x) (R.gE g y) = inner ℂ x y

def GEquivC : Prop :=
  ∀ t (g : G) (x : A.fam.amb.FR t), R.Th t (R.jX t (A.fam.amb.opR t (Sum.inr g) x)) = R.gE g (R.Th t (R.jX t x))

def LevTypeC (b : Bool) : Prop :=
  ∀ x : R.HE.H, R.HE.e x ∈ R.EEat (R.levR F b) ↔
    ∀ h : (F.lvl b).P, R.gE (h : G) x = D.what₂.embLL (((F.lvl b).ψ h : D.what₂.LLˣ) : D.what₂.LL) • x

def GUnitLC : Prop :=
  ∀ i (g : G) (x y : (R.HW i (sg0 D A)).H), inner ℂ (R.gW i (sg0 D A) g x) (R.gW i (sg0 D A) g y) = inner ℂ x y

def GEquivLC : Prop :=
  ∀ i t (g : G) (x : A.fam.amb.FL i t),
    R.thG i t (R.jV i t (A.fam.amb.opL i t (Sum.inr g) x)) = R.gW i (sg0 D A) g (R.thG i t (R.jV i t x))

def LevTypeLC (b : Bool) : Prop :=
  ∀ i (x : (R.HW i (sg0 D A)).H), (R.HW i (sg0 D A)).e x ∈ R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ↔
    (R.HW i (sg0 D A)).e x ∈ R.Wat i (sg0 D A) R.triv ∧
      ∀ h : (F.lvl b).P, R.gW i (sg0 D A) (h : G) x = sg0 D A ((((F.lvl b).ψ h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • x

def LiftsAll : Prop :=
  LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) ∧
    (∀ t j, j < D.R.m → LiftsExist (Yc D j) (R.βY j) (R.datYt t j R.triv)) ∧
    (∀ t, LiftsExist D.sp.X' R.βX (R.datXt t)) ∧
    (∀ i, LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv)) ∧
    (∀ i t, LiftsExist (Vc D i) (R.βV i) (R.datVt i t))

variable {R} in

def IrrX (A : FamIn D.what₂.LL G Pl0 T D.R.m) : Prop := ∀ χ ∈ A.X, IsAbsIrrChar χ

def MultAdd {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) : Prop :=
  ∀ T T' : MMap M, IsMultMap θ M J χ T → IsMultMap θ M J χ T' → IsMultMap θ M J χ (T + T')

def ActTieX : Prop :=
  ∀ t (g : G) (x : A.fam.amb.FR t), fX R t (R.jX t (A.fam.amb.opR t (Sum.inr g) x)) = actX R t g ∘ₗ fX R t (R.jX t x)

def EquivIoX : Prop :=
  ∀ t (g : G) (F F' : LinearMap.range (fX R t)),
    (F' : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) = actX R t g ∘ₗ (F : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) →
      ((R.ioX t F' : R.CC t (D.R.m - 1)) : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] (GA D (Yc D (D.R.m - 1)) → ℂ)) =
        actYt R t (D.R.m - 1) g ∘ₗ
          ((R.ioX t F : R.CC t (D.R.m - 1)) : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] (GA D (Yc D (D.R.m - 1)) → ℂ))

def EquivIoY : Prop :=
  ∀ t k, k + 1 < D.R.m → ∀ (g : G) (F F' : R.CC t (k + 1)),
    (F' : SmT (R.MY (k + 1)) →ₗ[ℂ] (GA D (Yc D (k + 1)) → ℂ)) =
        actYt R t (k + 1) g ∘ₗ (F : SmT (R.MY (k + 1)) →ₗ[ℂ] (GA D (Yc D (k + 1)) → ℂ)) →
      ((R.ioY t k F' : R.CC t k) : SmT (R.MY k) →ₗ[ℂ] (GA D (Yc D k) → ℂ)) =
        actYt R t k g ∘ₗ ((R.ioY t k F : R.CC t k) : SmT (R.MY k) →ₗ[ℂ] (GA D (Yc D k) → ℂ))

def ThFEquiv : Prop :=
  ∀ i t (g : G) (x : A.fam.amb.FL i t),
    R.thF i t (R.jV i t (A.fam.amb.opL i t (Sum.inr g) x)) = postOn (R.MW i (sg0 D A)) (actW R i g) (R.thF i t (R.jV i t x))

def GUnitOf : Prop := R.IsModels → LiftsAll R → UnimodGA (Yc D 0) → GUnitC R

def GEquivOf : Prop :=
  R.IsModels → R.IsChain → LiftsAll R → IrrX A → ActTieX R → EquivIoX R → EquivIoY R → GEquivC R

def LevTypeOf (b : Bool) : Prop :=
  R.IsModels → LiftsAll R →
    MultAdd R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) →
      LevTypeC R F b

def GUnitLOf : Prop := R.IsModels → LiftsAll R → (∀ i, UnimodGA (Wc D i)) → GUnitLC R

def GEquivLOf : Prop := R.IsModels → R.IsThP → LiftsAll R → IrrX A → ThFEquiv R → GEquivLC R

def LevTypeLOf (b : Bool) : Prop :=
  R.IsModels → LiftsAll R →
    (∀ i, MultAdd R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv))) →
      LevTypeLC R F b

end Defs

end Formalism.IndefR.Eqv.Act

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedContinuous
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem theta_bounded (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∃ B : ℝ, ∀ w, ‖f w‖ ≤ B := by
  obtain ⟨K, hK, hFK⟩ := Formalism.IndefR.PHeisFC.FD_sub_compact T S
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hf.cont.norm.continuousOn)
  refine ⟨B, fun w => ?_⟩
  obtain ⟨g, hg, -⟩ := Formalism.IndefR.PHeisFC.exU T S w
  obtain ⟨γ, hγ⟩ := g.2
  have h1 : f (g +ᵥ w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w := by
    rw [AddSubgroup.vadd_def, vadd_eq_add, ← hγ]
    exact hf.quasi γ w
  have h2 := hB _ (hFK hg)
  rw [h1, norm_mul, Formalism.IndefR.Fin.psi_norm hψ, one_mul, norm_norm] at h2
  exact h2

end Formalism.IndefR.Eqv

end
end

