import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0029
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0052
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivOutsideMul
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeAct

section General

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GAf L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) = 1
  rw [Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, Matrix.one_mul]

theorem trivOutside_inv {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GAf L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro v hv
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v hv, Matrix.mul_one] at e

theorem commute_of_ne {v w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hvw : v ≠ w) {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {w} y) : Commute x y := by
  show x * y = y * x
  apply Subtype.ext; apply Units.ext
  show (x.1 : Matrix (Fin n) (Fin n) (AL L)) * y.1 = (y.1 : Matrix (Fin n) (Fin n) (AL L)) * x.1
  ext i k
  rw [← sub_eq_zero]
  apply GlobalTheory.InertUmax.eq_zero_of_compAt L
  intro u
  rw [map_sub, sub_eq_zero]
  have hmx : ∀ A B : Matrix (Fin n) (Fin n) (AL L),
      compAt L u ((A * B) i k) = (A.map (compAt L u) * B.map (compAt L u)) i k := by
    intro A B; rw [← Matrix.map_mul]; rfl
  rw [hmx, hmx]
  by_cases hu : u = v
  · subst hu
    rw [hy u (by simpa using hvw), mul_one, one_mul]
  · rw [hx u (by simpa using hu), mul_one, one_mul]

variable {g : ℕ} [Fact g.Prime]

theorem isLiftAt_mul {s : SplitPlace L} {j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)}
    {y y' : GL (Fin n) ℤ_[g]} {x x' : GAf L n} (h : IsLiftAt s j y x) (h' : IsLiftAt s j y' x') :
    IsLiftAt s j (y * y') (x * x') :=
  ⟨trivOutside_mul h.1 h'.1, by rw [map_mul, h.2, h'.2, map_mul, map_mul]⟩

theorem isLiftAt_inv {s : SplitPlace L} {j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)}
    {y : GL (Fin n) ℤ_[g]} {x : GAf L n} (h : IsLiftAt s j y x) : IsLiftAt s j y⁻¹ x⁻¹ :=
  ⟨trivOutside_inv h.1, by rw [map_inv, h.2, map_inv, map_inv]⟩

theorem exists_isLiftAt (s : SplitPlace L) (j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L))
    (y : GL (Fin n) ℤ_[g]) : ∃ x : GAf L n, IsLiftAt s j y x :=
  GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s _

end General

section Fix

variable (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E)
    (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E))
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A)

theorem fix_of_mem {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) (hy : GlobalTheory.GLp.red (D.host.g k) D.R.r y = 1) :
    ρA x z = z := by
  simp only [KFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz
  exact hz k v ⟨y, hy⟩ x hl

theorem eq_of_red_eq {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k}
    {y y' : GL (Fin D.R.r) ℤ_[D.host.g k]} {x x' : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x)
    (hl' : IsLiftAt (s k v) (j k v) y' x')
    (he : GlobalTheory.GLp.red (D.host.g k) D.R.r y = GlobalTheory.GLp.red (D.host.g k) D.R.r y') : ρA x z = ρA x' z := by
  have h1 := fix_of_mem D s j ρA hz (isLiftAt_mul (isLiftAt_inv hl) hl') (by rw [map_mul, map_inv, he, inv_mul_cancel])
  symm
  calc ρA x' z = ρA x (ρA (x⁻¹ * x') z) := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = ρA x z := by rw [h1]

variable {D s j}

theorem map_mem (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v))
    {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) : ρA x z ∈ KFix D s j ρA := by
  simp only [KFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  rintro k' v' ⟨y', hy'⟩ x' hl'
  by_cases h : (⟨k', v'⟩ : Σ k : Fin 2, D.nd.PlG k) = ⟨k, v⟩
  · obtain ⟨rfl, hv⟩ := Sigma.mk.inj_iff.mp h
    cases eq_of_heq hv
    have h1 := fix_of_mem D s j ρA hz (isLiftAt_mul (isLiftAt_mul (isLiftAt_inv hl) hl') hl)
      (by rw [map_mul, map_mul, map_inv, hy', mul_one, inv_mul_cancel])
    rw [← Module.End.mul_apply, ← map_mul]
    conv_rhs => rw [← h1]
    rw [← Module.End.mul_apply, ← map_mul]
    simp only [mul_assoc, mul_inv_cancel_left]
  · have hne : (s k' v').v ≠ (s k v).v := fun e => h (hinj e)
    rw [← Module.End.mul_apply, ← map_mul, (commute_of_ne hne hl'.1 hl.1).eq, map_mul, Module.End.mul_apply,
      fix_of_mem D s j ρA hz hl' hy']

variable (D s j)

def liftAt (k : Fin 2) (v : D.nd.PlG k) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) : GAf D.host.E D.R.r :=
  Classical.choose (exists_isLiftAt (n := D.R.r) (s k v) (j k v)
    (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h))

theorem isLiftAt_liftAt (k : Fin 2) (v : D.nd.PlG k) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) :
    IsLiftAt (s k v) (j k v) (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h)
      (liftAt D s j k v h) :=
  Classical.choose_spec (exists_isLiftAt (n := D.R.r) (s k v) (j k v) _)

theorem red_surjInv (k : Fin 2) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) :
    GlobalTheory.GLp.red (D.host.g k) D.R.r (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h) = h :=
  Function.surjInv_eq _ h

theorem liftAt_apply {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) :
    ρA (liftAt D s j k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z = ρA x z :=
  eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v _) hl (red_surjInv D k _)

def factAct (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v)) (k : Fin 2)
    (v : D.nd.PlG k) : GL (Fin D.R.r) (ZMod (D.host.g k)) →* Module.End ℂ (KFix D s j ρA) where
  toFun h := (ρA (liftAt D s j k v h)).restrict (fun z hz => map_mem ρA hinj hz (isLiftAt_liftAt D s j k v h))
  map_one' := by
    apply LinearMap.ext; rintro ⟨z, hz⟩
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Module.End.one_apply]
    have := eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v 1) (⟨?_, ?_⟩ : IsLiftAt (s k v) (j k v) 1 1)
      (by rw [red_surjInv, map_one])
    · rw [this, map_one, Module.End.one_apply]
    · intro u _; exact Matrix.map_one _ (map_zero _) (map_one _)
    · rw [map_one, map_one, map_one]
  map_mul' a b := by
    apply LinearMap.ext; rintro ⟨z, hz⟩
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Module.End.mul_apply]
    rw [eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v (a * b))
      (isLiftAt_mul (isLiftAt_liftAt D s j k v a) (isLiftAt_liftAt D s j k v b))
      (by rw [red_surjInv, map_mul, red_surjInv, red_surjInv]), map_mul, Module.End.mul_apply]

theorem factAct_apply (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v))
    {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]} {x : GAf D.host.E D.R.r}
    (hl : IsLiftAt (s k v) (j k v) y x) (z : KFix D s j ρA) :
    ((factAct D s j ρA hinj k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y) z : KFix D s j ρA) : A) = ρA x z :=
  liftAt_apply D s j ρA z.2 hl

theorem factAct_commute (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v)) :
    Pairwise fun (a b : Σ k : Fin 2, D.nd.PlG k) => ∀ (x : GL (Fin D.R.r) (ZMod (D.host.g a.1)))
      (y : GL (Fin D.R.r) (ZMod (D.host.g b.1))),
      Commute (factAct D s j ρA hinj a.1 a.2 x) (factAct D s j ρA hinj b.1 b.2 y) := by
  rintro ⟨k, v⟩ ⟨k', v'⟩ hne x y
  have hv : (s k v).v ≠ (s k' v').v := fun e => hne (hinj e)
  have hc := commute_of_ne hv (isLiftAt_liftAt D s j k v x).1 (isLiftAt_liftAt D s j k' v' y).1
  apply LinearMap.ext; rintro ⟨z, hz⟩
  apply Subtype.ext
  show ρA (liftAt D s j k v x) (ρA (liftAt D s j k' v' y) z) = ρA (liftAt D s j k' v' y) (ρA (liftAt D s j k v x) z)
  rw [← Module.End.mul_apply, ← map_mul, hc.eq, map_mul, Module.End.mul_apply]

end Fix

theorem exists_rep : ∀ (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E) (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)), Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v) → ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A), ∃ ρ : Representation ℂ (G0g D.nd) (KFix D s j ρA), ∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → ∀ z : KFix D s j ρA, ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ρA) : A) = ρA x z := by
  intro D s j hinj A _ _ ρA
  classical
  refine ⟨MonoidHom.noncommPiCoprod (fun kv => factAct D s j ρA hinj kv.1 kv.2) (factAct_commute D s j ρA hinj), ?_⟩
  intro k v y x hl z
  rw [GlobalTheory.GoodTypes.facHom, MonoidHom.mulSingle_apply, MonoidHom.noncommPiCoprod_mulSingle]
  exact factAct_apply D s j ρA hinj hl z

end GlobalTheory.TypeAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachShiftMemOfExpansions
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

section Core

open TensorProduct Formalism.MainNotions.RamifiedCoefficientChains.Sh Formalism.MainNotions.N.Pv.LocalLengthBound.Ser Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt
open Formalism.MainNotions.CrystallineLiftingInputs (DL)
open Formalism.MainNotions.LiftingTheory (qp)
open Formalism.MainNotions.WachCoordinates (FilLev)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem wachExp_diag_shift_iff {M : Type} [AddCommGroup M] [Module LL M] {Fl : ℤ → Submodule LL M}
    (hF : Antitone Fl) {m : ℤ} {d : ℤ → M} (hd : ∀ k < m, d k = 0) (u : PowerSeries LL)
    (hu : IsUnit u) (y : ℕ) :
    (∀ k, conv ((u * PowerSeries.X) ^ y) d k ∈ Fl (-k)) ↔ ∀ k, d k ∈ Fl (-k - y) := by
  have hd' : LB m d := hd
  have hu0 : PowerSeries.constantCoeff (u ^ y) ≠ 0 :=
    ((hu.pow y).map PowerSeries.constantCoeff).ne_zero
  have e : conv ((u * PowerSeries.X) ^ y) d = fun k => smulS (u ^ y) d (k - y) := by
    show smulS ((u * PowerSeries.X) ^ y) d = _
    rw [mul_comm, mul_pow, smulS_mul hd', smulS_X_pow (LB_smulS hd' _)]
  rw [e]
  constructor
  · intro h k
    have h1 : Dg Fl (-(y : ℤ)) (smulS (u ^ y) d) := fun j => by
      have := h (j + y)
      simp only [add_sub_cancel_right] at this
      rwa [show -(y : ℤ) - j = -(j + y) by ring]
    have h2 := Dg_smulS hF (LB_smulS hd' _) h1 (u ^ y)⁻¹ k
    rw [smulS_inv hd' _ hu0] at h2
    rwa [show -k - (y : ℤ) = -(y : ℤ) - k by ring]
  · intro h k
    have h1 : Dg Fl (-(y : ℤ)) d := fun j => by
      rw [show -(y : ℤ) - j = -j - y by ring]; exact h j
    have h2 := Dg_smulS hF hd' h1 (u ^ y) (k - y)
    rwa [show -(y : ℤ) - (k - y) = -k by ring] at h2

theorem wachExp_mem_iff (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hRg : ExpRing W)
    (hRu : ExpRules W) (hCr : ExpCrit W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR) (hx : DL W T i x) (hd : IsExp W T i ζ x d)
    (Y : ℕ) (hY : qp W ^ Y • x ∈ W.N T) (y : ℕ) :
    qp W ^ y • x ∈ W.N T ↔ ∀ k, d k ∈ FilLev W T i 0 (-k - y) := by
  have hK : Module.finrank K₀ K = 1 := Formalism.MainNotions.UnusedSlot80.SatW.finrank_one_of_bij' hA.1
  obtain ⟨h9r, -⟩ := (h9 T hT hA.2.1 hA.2.2).2.2 hK
  have hR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W h9r
  have hqΔ := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hR.πΔ
  have hDL : DL W T i (qp W ^ y • x) := by
    refine ⟨by rw [smul_comm, hx.1], fun δ hδ => ?_⟩
    rw [γD_smul', map_pow, hqΔ δ hδ, hx.2 δ hδ]
  obtain ⟨⟨u, hu, hq⟩, -, -⟩ := hRg hA i ζ hζ
  have hE := (hRu hA T hT i ζ hζ).2.2.2.2.1 (qp W ^ y) x d hd
  have hN : qp W ^ Y • (qp W ^ y • x) ∈ W.N T := by
    rw [smul_comm]; exact (W.N T).smul_mem _ hY
  rw [(hCr hA T hT i ζ hζ _ _ hDL hE).1 ⟨Y, hN⟩, map_pow, hq]
  obtain ⟨m, hm⟩ := hd.1
  exact wachExp_diag_shift_iff (Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0) hm u hu y

theorem wachShift_mem_of_exp [NeZero n] (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRg : ExpRing W) (hRu : ExpRules W) (hCr : ExpCrit W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hp : (PD.p : LL) ≠ 0) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (y' Y : ℕ) (cO : ℤ → O)
    (hc : ∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O))
    (xs : List ℤ)
    (hxs : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i → IsJumpV PD T.ρ τ a →
      y' < j → j ≤ Y → a + (j : ℤ) ∈ xs)
    (seq : ℕ → W.DD T) (h0 : DL W T i (seq 0)) (h0N : qp W ^ Y • seq 0 ∈ W.N T)
    (hrec : ∀ k < xs.length, W.π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) =
      W.γD T W.gam (seq k) - seq k) :
    DL W T i (seq xs.length) ∧ qp W ^ y' • seq xs.length ∈ W.N T := by
  classical
  have hU := Formalism.MainNotions.UnusedSlot35.DssRec.π₀_unit W h9 hA T hT
  have hDS := rToolMod_dStab W h9
  have hQ : ∀ k ≤ xs.length, QLattice W T i Y (seq k) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨h0, h0N⟩
    | succ k ih =>
      intro hk
      have hk' : k < xs.length := hk
      have e : seq (k + 1) = derivationOnWachModule W T (seq k) + (-cO (xs.getD k 0)) • seq k := by
        have h1 : seq (k + 1) + cO (xs.getD k 0) • seq k = derivationOnWachModule W T (seq k) :=
          Formalism.MainNotions.UnusedSlot35.DssRec.smul_inj W.π₀ hU (by rw [hrec k hk', uniformizer_smul_derivation W T hU]; rfl)
        rw [← h1, neg_smul, add_neg_cancel_right]
      rw [e]
      exact qLattice_add W T (qLattice_derivation W T hDS hA hT i Y (ih hk'.le))
        (qLattice_smul W T _ (ih hk'.le))
  refine ⟨(hQ _ le_rfl).1, ?_⟩
  obtain ⟨⟨u, hu, hq⟩, hπ0, -⟩ := hRg hA i ζ hζ
  obtain ⟨hex, -, hadd, hsO, hsA, hγ, -⟩ := hRu hA T hT i ζ hζ
  have hqne : W.lev i ζ (qp W ^ Y) ≠ 0 := by
    rw [map_pow, hq]
    exact pow_ne_zero _ (mul_ne_zero hu.ne_zero PowerSeries.X_ne_zero)
  have hf : ∀ k : ℕ, ∃ d : ℤ → T.V ⊗[Qp] BdR, (∃ m : ℤ, ∀ j < m, d j = 0) ∧
      (k ≤ xs.length → IsExp W T i ζ (seq k) d) := by
    intro k
    by_cases hk : k ≤ xs.length
    · obtain ⟨d, hd, -⟩ := hex (seq k) _ (hQ k hk).2 hqne
      exact ⟨d, hd.1, fun _ => hd⟩
    · exact ⟨0, ⟨0, fun _ _ => rfl⟩, fun h => absurd h hk⟩
  choose f hfb hfe using hf
  rw [wachExp_mem_iff W h9 hRg hRu hCr hA T hT i ζ hζ _ _ (hQ _ le_rfl).1 (hfe _ le_rfl) Y
    (hQ _ le_rfl).2 y']
  have hf0 := (wachExp_mem_iff W h9 hRg hRu hCr hA T hT i ζ hζ _ _ h0 (hfe 0 (Nat.zero_le _)) Y
    h0N Y).1 h0N
  let uL : LLˣ := Units.map (algebraMap O LL : O →* LL) (W.χΓ W.gam)
  refine filtLaurent_shift_line LL _ (fun a => FilLev W T i 0 a)
    (Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0) uL (W.lev i ζ W.π₀) (fun x => algebraMap O LL (cO x))
    (by rw [hπ0]; exact neg_ne_zero.2 hp) (fun x => ?_) y' Y xs (fun a j ha hj hj' => ?_) f hfb
    (fun m hm k => ?_) hf0
  · have h1 := congrArg (algebraMap O LL) (hc x)
    rw [map_mul, map_natCast, map_sub, map_one] at h1
    have h2 : ((uL ^ (-x) : LLˣ) : LL) = algebraMap O LL (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) := by
      rw [← map_zpow]; rfl
    rw [hπ0, h2]
    linear_combination -h1
  · let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hA.1
    let τ : K →ₐ[Qp] LL := (W.emb i).comp e.symm.toAlgHom
    have hτ : Formalism.MainNotions.LiftingTheory.Over W τ i := by
      apply AlgHom.ext
      intro z
      show W.emb i (e.symm (e z)) = W.emb i z
      rw [e.symm_apply_apply]
    have hF : ∀ b : ℤ, FildR PD T.ρ τ b = FilLev W T i 0 b := by
      intro b
      rw [((hD hA.1 T.V T.ρ hT).2 τ).2.2 b, show τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i from hτ]
      unfold FilLev
      simp only [Nat.cast_zero, sub_zero, pow_zero, Module.End.one_eq_id, Submodule.map_id]
    refine hxs τ a j hτ ?_ hj hj'
    unfold IsJumpV
    rw [hF, hF]
    exact ha
  · have e1 := hfe m hm.le
    have e2 := hfe (m + 1) hm
    have hL := hsA W.π₀ _ _ (hadd _ _ _ _ e2 (hsO (cO (xs.getD m 0)) _ _ e1))
    have hR := hadd _ _ _ _ (hγ _ _ e1) (hsO (-1) _ _ e1)
    have ex : W.γ T (seq m) + (-1 : O) • seq m =
        W.π₀ • (seq (m + 1) + cO (xs.getD m 0) • seq m) := by
      rw [hrec m hm, neg_one_smul, ← sub_eq_add_neg]; rfl
    rw [ex] at hR
    have hN : qp W ^ Y • (W.π₀ • (seq (m + 1) + cO (xs.getD m 0) • seq m)) ∈ W.N T := by
      rw [smul_comm]
      exact (W.N T).smul_mem _
        (qLattice_add W T (hQ (m + 1) hm) (qLattice_smul W T _ (hQ m hm.le))).2
    have h3 := congrFun ((hex _ _ hN hqne).unique hL hR) k
    have h2 : ((uL ^ k : LLˣ) : LL) = (algebraMap O LL (W.χΓ W.gam : O)) ^ k := by
      rw [Units.val_zpow_eq_zpow_val]; rfl
    rw [h2, sub_smul, one_smul]
    refine Eq.trans ?_ (h3.trans ?_)
    · rfl
    · simp [sub_eq_add_neg]

end Core

theorem wachShift_mem_of_expansions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc), ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (y' Y : ℕ) (cO : ℤ → ↥(OL LL)), (∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - (((((HW l).W K 1 LL hA.2.2).χΓ ((HW l).W K 1 LL hA.2.2).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) → ∀ xs : List ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hA.2.2) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ((HW l).W K 1 LL hA.2.2).DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ Y • seq 0 ∈ ((HW l).W K 1 LL hA.2.2).N T → (∀ k < xs.length, ((HW l).W K 1 LL hA.2.2).π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) = ((HW l).W K 1 LL hA.2.2).γD T ((HW l).W K 1 LL hA.2.2).gam (seq k) - seq k) → Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ y' • seq xs.length ∈ ((HW l).W K 1 LL hA.2.2).N T := by
  intro D HW l _ K LL hA h9 hRg hRu hCr hD T hT i y' Y cO hc xs hxs seq h0 h0N hrec
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := Formalism.MainNotions.UnusedSlot80.exists_prim_of_good D hA.2.2
  refine wachShift_mem_of_exp _ h9 hRg hRu hCr hD
    (Formalism.MainNotions.UnusedSlot80.caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1) ?_ ζ (by rw [hp]; exact hζ) T hT i y' Y
    cO (fun x => by rw [hp]; exact hc x) xs hxs seq h0 h0N hrec
  rw [hp]
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

end GlobalTheory
end

