import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0865
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChartValIndepOfHarmonic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCanonGaugeNabValBoundedDenom
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsExtAllModelsUniformised
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0056
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScale
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0114
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0117
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0052
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexSplitPlaceEqMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.SplitLatIdx

theorem relIndex_map_of_proj {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : AddSubgroup X) (φ P : X →+ X)
    (pr : X →+ Y) (hK : ∀ x, pr x = 0 → P x = 0) (hPA : ∀ a ∈ A, P a ∈ A)
    (hφ : ∀ x, φ x - P (φ x) = x - P x) (hc : ∀ x, P (φ x) = φ (P x)) :
    (A.map φ).relIndex A = ((A.map φ).map pr).relIndex (A.map pr) := by
  rw [← AddSubgroup.relIndex_comap ((A.map φ).map pr) pr A, ← AddSubgroup.inf_relIndex_right (A.map φ) A,
    ← AddSubgroup.inf_relIndex_right (((A.map φ).map pr).comap pr) A]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  refine ⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩
  rintro ⟨⟨y, ⟨a, ha, rfl⟩, hy⟩, hx⟩
  refine ⟨⟨a + (x - φ a), ?_, ?_⟩, hx⟩
  · have hPz : P (x - φ a) = 0 := hK _ (by rw [map_sub, hy, sub_self])
    have hz : x - φ a = (x - P x) - (a - P a) := by
      calc x - φ a = (x - φ a) - P (x - φ a) := by rw [hPz, sub_zero]
        _ = (x - P x) - (φ a - P (φ a)) := by rw [map_sub]; abel
        _ = _ := by rw [hφ a]
    refine add_mem ha ?_
    rw [hz]
    exact sub_mem (sub_mem hx (hPA x hx)) (sub_mem ha (hPA a ha))
  · have hPz : P (x - φ a) = 0 := hK _ (by rw [map_sub, hy, sub_self])
    have h1 := hφ (x - φ a)
    simp only [hc, hPz, map_zero, sub_zero] at h1
    rw [map_add, h1]
    abel

end GlobalTheory.SplitLatIdx

namespace GlobalTheory.SplitLatIdx

set_option maxHeartbeats 1600000 in

theorem latIndex_split : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → w ≠ w' → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g * GlobalTheory.LocKerMod.idxAt T w' h' g := by
  intro D T v w w' h h' hv hne g
  classical
  obtain ⟨w'', -, hu, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place (isCMExt_host D) h hv
  have hover : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v → u = w ∨ u = w' := by
    intro u hu0
    rcases (hu u).1 hu0 with e | e
    · exact Or.inl e
    · rcases (hu w').1 h' with e' | e'
      · exact absurd e'.symm hne
      · exact Or.inr (e.trans e'.symm)
  set M := finMat D.sp.cm.sig T.gram (GlobalTheory.FinZeta.embV T v g) with hMdef
  have hcomp : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (y : Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (i : Fin T.rank),
      GlobalTheory.LFun.compAt D.host.F u ((M *ᵥ y) i) = (M.map (GlobalTheory.LFun.compAt D.host.F u) *ᵥ fun j => GlobalTheory.LFun.compAt D.host.F u (y j)) i :=
    fun u y i => RingHom.map_mulVec _ M y i
  have hMw : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (hh : u.under (𝓞 D.host.F) = v),
      M.map (GlobalTheory.LFun.compAt D.host.F u) = (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram hh g).1 := by
    intro u hh
    have e := GlobalTheory.LFun.finMat_map_compAt D.sp.cm.sig T.gram hh (GlobalTheory.FinZeta.embV T v g)
    rw [proj_emb_self] at e
    exact e
  have hMu : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) ≠ v → M.map (GlobalTheory.LFun.compAt D.host.F u) = 1 := by
    intro u hh
    have e := GlobalTheory.LFun.finMat_map_compAt D.sp.cm.sig T.gram (rfl : u.under (𝓞 D.host.F) = _) (GlobalTheory.FinZeta.embV T v g)
    rw [proj_emb_ne _ _ hh, map_one, Units.val_one] at e
    exact e
  set ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E := GlobalTheory.LFun.singleAt D.host.F w 1 + GlobalTheory.LFun.singleAt D.host.F w' 1 with hεdef
  have hεw : GlobalTheory.LFun.compAt D.host.F w ε = 1 := by
    rw [hεdef, map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne hne, add_zero]
  have hεw' : GlobalTheory.LFun.compAt D.host.F w' ε = 1 := by
    rw [hεdef, map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne (Ne.symm hne), zero_add]
  have hεu : ∀ u, u ≠ w → u ≠ w' → GlobalTheory.LFun.compAt D.host.F u ε = 0 := by
    intro u h1 h2
    rw [hεdef, map_add, GlobalTheory.LFun.compAt_singleAt_ne h1, GlobalTheory.LFun.compAt_singleAt_ne h2, add_zero]
  have hεint : ε ∈ intAE D :=
    add_mem (GlobalTheory.LFun.singleAt_mem_intAE (one_mem _)) (GlobalTheory.LFun.singleAt_mem_intAE (one_mem _))
  let pr : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin T.rank → w.adicCompletion D.host.E) × (Fin T.rank → w'.adicCompletion D.host.E) :=
    AddMonoidHom.mk' (fun x => (fun i => GlobalTheory.LFun.compAt D.host.F w (x i), fun i => GlobalTheory.LFun.compAt D.host.F w' (x i)))
      (fun x y => by ext i <;> simp)
  let P : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun x i => ε * x i) (fun x y => by funext i; simp [mul_add])
  let φ := M.mulVecLin.toAddMonoidHom
  have hφa : ∀ x, φ x = M *ᵥ x := fun x => rfl
  have hK : ∀ x, pr x = 0 → P x = 0 := by
    intro x hx
    have h1 : ∀ i, GlobalTheory.LFun.compAt D.host.F w (x i) = 0 := fun i => congrFun (congrArg Prod.fst hx) i
    have h2 : ∀ i, GlobalTheory.LFun.compAt D.host.F w' (x i) = 0 := fun i => congrFun (congrArg Prod.snd hx) i
    funext i
    refine GlobalTheory.LFun.compAt_ext fun u => ?_
    show GlobalTheory.LFun.compAt D.host.F u (ε * x i) = GlobalTheory.LFun.compAt D.host.F u 0
    rw [map_mul, map_zero]
    by_cases e1 : u = w
    · subst e1; rw [h1 i, mul_zero]
    by_cases e2 : u = w'
    · subst e2; rw [h2 i, mul_zero]
    rw [hεu u e1 e2, zero_mul]
  have hPA : ∀ a ∈ Formalism.L2.NTheta.LamHat T, P a ∈ Formalism.L2.NTheta.LamHat T :=
    fun a ha => (GlobalTheory.LatDual.lamHat_selfDual_and_module T).2 ε hεint a ha
  have hφ : ∀ x, φ x - P (φ x) = x - P x := by
    intro x
    funext i
    refine GlobalTheory.LFun.compAt_ext fun u => ?_
    show GlobalTheory.LFun.compAt D.host.F u ((M *ᵥ x) i - ε * (M *ᵥ x) i) = GlobalTheory.LFun.compAt D.host.F u (x i - ε * x i)
    rw [map_sub, map_sub, map_mul, map_mul]
    by_cases e : u = w ∨ u = w'
    · have : GlobalTheory.LFun.compAt D.host.F u ε = 1 := by rcases e with rfl | rfl; exacts [hεw, hεw']
      rw [this, one_mul, one_mul, sub_self, sub_self]
    · push_neg at e
      have hv' : u.under (𝓞 D.host.F) ≠ v := fun hh => by rcases hover u hh with e' | e' <;> [exact e.1 e'; exact e.2 e']
      rw [hεu u e.1 e.2, zero_mul, zero_mul, hcomp, hMu u hv', Matrix.one_mulVec]
  have hc : ∀ x, P (φ x) = φ (P x) := by
    intro x
    show (fun i => ε * (M *ᵥ x) i) = M *ᵥ (fun j => ε * x j)
    have e : (fun j => ε * x j) = ε • x := rfl
    rw [e, Matrix.mulVec_smul]
    rfl
  have hprφ : ∀ y, pr (φ y) = ((GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1 *ᵥ fun i => GlobalTheory.LFun.compAt D.host.F w (y i),
      (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' g).1 *ᵥ fun i => GlobalTheory.LFun.compAt D.host.F w' (y i)) := by
    intro y
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show GlobalTheory.LFun.compAt D.host.F w ((M *ᵥ y) i) = _
      rw [hcomp, hMw w h]
    · show GlobalTheory.LFun.compAt D.host.F w' ((M *ᵥ y) i) = _
      rw [hcomp, hMw w' h']
  have hsg : ∀ (x : Fin T.rank → w.adicCompletion D.host.E) (x' : Fin T.rank → w'.adicCompletion D.host.E),
      pr (fun i => GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = (x, x') := by
    intro x x'
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show GlobalTheory.LFun.compAt D.host.F w (GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = x i
      rw [map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne hne, add_zero]
    · show GlobalTheory.LFun.compAt D.host.F w' (GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = x' i
      rw [map_add, GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne (Ne.symm hne), zero_add]
  have hsgm : ∀ (x : Fin T.rank → w.adicCompletion D.host.E) (x' : Fin T.rank → w'.adicCompletion D.host.E),
      x ∈ GlobalTheory.LFun.latAt w (frameLat T) → x' ∈ GlobalTheory.LFun.latAt w' (frameLat T) →
      (fun i => GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) ∈ Formalism.L2.NTheta.LamHat T :=
    fun x x' hx hx' => add_mem (GlobalTheory.LFun.singleAt_mem_lamHat hx) (GlobalTheory.LFun.singleAt_mem_lamHat hx')
  have hmem : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) y, y ∈ Formalism.L2.NTheta.LamHat T →
      (fun i => GlobalTheory.LFun.compAt D.host.F u (y i)) ∈ GlobalTheory.LFun.latAt u (frameLat T) :=
    fun u y hy => GlobalTheory.LFun.compAt_mem_latAt u (hermitianSpaceBaseLattice_eq_frameLattice T ▸ hy)
  have hA : (Formalism.L2.NTheta.LamHat T).map pr =
      (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.prod (GlobalTheory.LFun.latAt w' (frameLat T)).toAddSubgroup := by
    ext ⟨x, x'⟩
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have e1 : (fun i => GlobalTheory.LFun.compAt D.host.F w (y i)) = x := congrArg Prod.fst hxy
      have e2 : (fun i => GlobalTheory.LFun.compAt D.host.F w' (y i)) = x' := congrArg Prod.snd hxy
      subst e1 e2
      exact ⟨hmem w y hy, hmem w' y hy⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨_, hsgm x x' hx hx', hsg x x'⟩
  have hB : ((Formalism.L2.NTheta.LamHat T).map φ).map pr =
      ((GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.map
        (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).prod
      ((GlobalTheory.LFun.latAt w' (frameLat T)).toAddSubgroup.map
        (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' g).1.mulVecLin.toAddMonoidHom) := by
    ext ⟨x, x'⟩
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, hxy⟩
      rw [hprφ] at hxy
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
      exact ⟨⟨_, hmem w a ha, rfl⟩, ⟨_, hmem w' a ha, rfl⟩⟩
    · rintro ⟨⟨b, hb, rfl⟩, ⟨b', hb', rfl⟩⟩
      refine ⟨φ _, ⟨_, hsgm b b' hb hb', rfl⟩, ?_⟩
      rw [hprφ]
      have e := hsg b b'
      simp only [pr, AddMonoidHom.mk'_apply, Prod.mk.injEq] at e
      rw [e.1, e.2]
      rfl
  show ((Formalism.L2.NTheta.LamHat T).map φ).relIndex (Formalism.L2.NTheta.LamHat T) = _
  rw [relIndex_map_of_proj _ φ P pr hK hPA hφ hc, hA, hB, GlobalTheory.BorelUMod.relIndex_prod_prod]
  rfl

end GlobalTheory.SplitLatIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShortThetaValueBoundedGoodReduction
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodThetaBound

section Parts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PlaceInt GlobalTheory.GoodPts
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem unif_of_splitModel {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (I : IntData Xo c T io y.1)
    (hS : PullbackSections.SplitModel I) : ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso := by
  have hprop : IsProper I.t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) I.m1.cart.1 Xo.univ.proper
  obtain ⟨j, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance I.G I.G I.t' hprop I.m2 I.m2
  have hp := GlobalTheory.UnifAfterExt.polAt_of_sabMap j I.m2 I.m1 Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK T.V) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨-, P, -, hP⟩ := GlobalTheory.UnifAfterExt.isOpen_and_uniformised T.V inferInstance I.G hp hS
  exact ⟨P, hP⟩

theorem root_pow_sq {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {N : ℕ} (hN : l.M ∣ N) (a : Dw.La)
    {t : ptO Xo x ⟶ Xo.univ.t.G} (ht : t ^ N = levPt Xo x a) : t ^ (N ^ 2) = 1 := by
  obtain ⟨k, hk⟩ := hN
  have h : levPt Xo x a ^ l.M = 1 := by
    rw [levPt, ← MonObj.comp_pow, (GlobalTheory.moduli_univ_eta_killed GlobalTheory.firstFiveLaws.1 E H Dw l Xo a).2.2, MonObj.comp_one]
  rw [pow_two, pow_mul, ht, hk, pow_mul, h, one_pow]

theorem reach_of_isUUOver {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {N : ℕ} (hN : Odd N) (s : SecN Xo x 1)
    {x₁ x₂ : ptO Xo x ⟶ Xo.univ.t.G} (h₁ : x₁ ^ (N ^ 2) = 1) (h₂ : x₂ ^ (N ^ 2) = 1)
    {F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo x))}
    (hF : IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F) : Reach Xo s (N ^ 2) (sqN Xo N F) := by
  obtain ⟨F₀, F₁, p, m₁, m₂⟩ := ((uu_through_moves E H Dw l Xo S x N hN s).1 x₁ x₂ F h₁ h₂).1 hF
  refine .move _ x₂ F₁ _ (.move _ x₁ F₀ F₁ (.pull 1 (N ^ 2) (N ^ 2) (N : 𝓞 E) s F₀ .base (.inl rfl) hN.pow ?_
    (Nat.one_mul _).symm p) m₁) m₂
  rw [map_natCast, Nat.cast_pow, pow_two]

theorem splitModel_of_good {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (hy : GoodPts.Good y)
    (I : IntData Xo c T io y.1) : PullbackSections.SplitModel I := by
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, hG⟩ := hy
  obtain ⟨-, n, -⟩ := GlobalTheory.ThetaBound.Prep.sab_extensions_iso E H Dw l Xo T.V T.Fr y.1.x I.G G I.t' t' I.m1 I.m2 m1 m2
  have hp : IsProper I.G.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n.cart.1 hG
  exact ⟨_, GlobalTheory.ZJ.isGt_splitExtOfAbelian _ (GlobalTheory.isAbelianScheme_pullback_obj _ _
    (isAbelianScheme_of_proper _ I.G.semi hp))⟩

theorem exists_ext [StarRing (𝓞 E)] (hstar : ∀ a : 𝓞 E, star a = H.bar a) {T : CDVR} {io : c.F →+* T.Fr}
    (y : IntFr Xo c T io) (hy : GoodPts.Good y) (M : ℕ) (hM : 0 < M) :
    ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io))
      (C' : IntegralChartA3 Xo c T' (iT.comp io) y'), IsExt y iT e y' ∧ Good3 C' ∧ AllRat Xo (xOf y') M := by
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists E H Dw l Xo c hstar T io y
  have hgood₁ : Good3 C₁ := ⟨hC₁, unif_of_splitModel C₁.I (splitModel_of_good y hy C₁.I)⟩
  obtain ⟨L, _, _, hL, hrat⟩ := (GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo T.Fr (xOf y) M hM).1
  obtain ⟨T₂, i₂, e₂, ψ, φ, he₂, hv₂, hψ, -, -⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
  obtain ⟨⟨y₂, hext₂⟩, hy⟩ := GlobalTheory.ThetaBound.exists_isExt_and_trans E H Dw l Xo c T T₂ io y i₂ e₂ he₂ hv₂
  have hx₂ := (hy y₂ hext₂).1
  obtain ⟨C₂, hgood₂⟩ :=
    GlobalTheory.ThetaBound.Prep.exists_good_chart_ext E H Dw l Xo c hstar T io y C₁ hgood₁ T₂ i₂ e₂ y₂ hext₂
  have hrat₂ := ((GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo L _ M hM).2 hrat).1 T₂.Fr ψ.toRingHom
  have hi : i₂ = ψ.toRingHom.comp (algebraMap T.Fr L) := RingHom.ext fun a => (hψ a).symm
  have hsp : spMap ψ.toRingHom ≫ spMap (algebraMap T.Fr L) ≫ xOf y = xOf y₂ := by
    rw [hx₂, hi, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  rw [hsp] at hrat₂
  exact ⟨T₂, i₂, e₂, y₂, C₂, hext₂, hgood₂, hrat₂⟩

theorem sum_degree_colOf {n : ℕ} (m : LtN Dw n →₀ ℕ) : ∑ b, (colOf m b).degree = m.degree := by
  simp only [Finsupp.degree_eq_sum, colOf, Finsupp.equivFunOnFinite_symm_apply_apply]
  rw [Finset.sum_comm, Fintype.sum_sigma, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun τ _ => (Fintype.sum_prod_type (fun p : Fin (Dw.mult τ) × Fin n => m ⟨τ, p⟩)).symm

theorem hv_bound [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) {T : CDVR} {io : c.F →+* T.Fr}
    (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (k n d : ℕ) (F : Fin n → SecN Xo (xOf y) k)
    (f : Fin n → PS T.V 1 (chD C.ch)) (hf : ∀ b, GermIs C k (F b) (f b)) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1)) (hd : P.IsHomogeneous d)
    (hc : ∀ m, InV T (io (P.coeff m))) :
    letI := io.toAlgebra
    InV T (((2 * NumberField.discr E : ℤ) : T.Fr) ^ d * hv Xo c nab y.1 k F P) := by
  letI := io.toAlgebra
  obtain ⟨B, hB, hB2⟩ := GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound E H Dw l Xo c hnab.1 T io y C
  obtain ⟨h', hg', hbd⟩ := GlobalTheory.GaugeBoundedDenom.exists_canonGauge_nabVal_bounded_denom T.V T.Fr E _ B _ (hB2 B hB).1
  have tk : ∀ {r : ℕ} (g : PS T.Fr r (chD C.ch)), FB.toK T.Fr g = g := fun g => by
    ext m
    simp
  have h1 : C.ch.B.FK T.Fr = B.FK T.Fr := by
    funext j
    simp only [FB.FK, FGLaw.mapF, hB.1, ← C.gen.1.1 j]
    simp
  have h2 : ∀ a, C.ch.B.actK T.Fr a = B.actK T.Fr a := by
    intro a
    funext j
    simp only [FB.actK, hB.2.1, ← C.gen.1.2.1 a j]
    simp
  have hg : C.ch.B.IsCanonGauge T.Fr h' := by
    refine ⟨hg'.ax0, hg'.ax1, ?_, ?_, ?_, fun a => ?_⟩
    · rw [h1, tk, ← hg'.ph1, hB.2.2.1]
      exact C.gen.1.2.2.1
    · rw [h1, tk, ← hg'.ph2, hB.2.2.2.1]
      exact C.gen.1.2.2.2.1
    · rw [tk, ← hg'.sy, hB.2.2.2.2.1]
      exact C.gen.1.2.2.2.2.1
    · rw [h2, h2, tk, ← hg'.ad, hB.2.2.2.2.2]
      exact C.gen.1.2.2.2.2.2.1 a
  let C' : ChartAt Xo c y.1 := { C.ch with h := h', gauge := hg }
  obtain ⟨C₀, hex, hpin⟩ := hnab.2 T.Fr y.1
  choose f₀ hf₀ using fun b => hex k (F b)
  have e₀ : ∀ m, ∏ b, nab y.1 k (F b) (colOf m b) =
      ∏ b, C₀.B.nabVal T.Fr C₀.h H.w0 k (f₀ b) C₀.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin k (F b) (f₀ b) (hf₀ b) (colOf m b)
  have h := GlobalTheory.HarmonicAny.chartVal_indep_of_harmonic E H Dw l Xo c hnab.1 T.Fr y.1 C₀ C' k n F f₀
    (fun b => MvPowerSeries.map (algebraMap T.V T.Fr) (f b)) hf₀ hf P hP
  have e₁ : hv Xo c nab y.1 k F P = chartVal C₀ k f₀ P := by
    simp only [hv, chartVal, e₀]
  rw [e₁, h, chartVal, Finset.mul_sum]
  refine Subring.sum_mem _ fun m hm => ?_
  have hm' : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hd (MvPolynomial.mem_support_iff.1 hm)
  rw [_root_.mul_left_comm, ← hm', ← sum_degree_colOf, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Subring.mul_mem _ (hc m) (Subring.prod_mem _ fun b _ => ?_)
  have hu : C.ch.uvec = fun ℓ i => algebraMap T.V T.Fr (C.uvecT ℓ i) :=
    funext fun ℓ => funext fun i => C.gen.1.2.2.2.2.2.2 ℓ i
  have key := hbd H.w0 k (f b) (Lt1 Dw) C.uvecT (colOf m b)
  rw [← hu] at key
  have e : C'.B.nabVal T.Fr C'.h H.w0 k (MvPowerSeries.map (algebraMap T.V T.Fr) (f b)) C'.uvec
      (MvPolynomial.monomial (colOf m b) 1) =
      B.nabVal T.Fr h' H.w0 k (FB.toK T.Fr (f b)) C.ch.uvec (MvPolynomial.monomial (colOf m b) 1) := by
    change C.ch.B.nabVal T.Fr h' H.w0 k (FB.toK T.Fr (f b)) C.ch.uvec _ = _
    simp only [FB.nabVal, FB.hL, h1, h2]
  rw [e]
  exact key

theorem inV_of_ext {T T' : CDVR} (iT : T.Fr →+* T'.Fr) {e : ℕ} (he : 0 < e)
    (hv : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) {x : T.Fr} : InV T' (iT x) ↔ InV T x := by
  constructor
  · rintro ⟨a, ha⟩
    have h := GlobalTheory.ThetaBound.Prep.vV_nonneg T' a
    rw [ha, hv] at h
    exact Formalism.L2.PjFree.mem_range_of_vV_nonneg
      (le_of_mul_le_mul_left (by simpa using h) (by exact_mod_cast he : (0 : ℤ) < e))
  · rintro ⟨a, rfl⟩
    exact Formalism.L2.PjFree.mem_range_of_vV_nonneg (by
      rw [hv]; exact mul_nonneg (by exact_mod_cast he.le) (GlobalTheory.ThetaBound.Prep.vV_nonneg T a))

theorem scalar_cases {K : Type} [Field K] [CharZero K] (m r N d d' : ℕ) (D : ℤ) (s : K) (h : d' = d ∨ s = 0) :
    ∃ ε : ℕ, ((m * r : ℕ) : K) * ((2 * D * N : ℤ) : K) ^ d *
      ((1 : K)⁻¹ * (m : K)⁻¹ * (r : K)⁻¹ * ((N : K) ^ d')⁻¹ * s) = ε * (((2 * D : ℤ) : K) ^ d * s) := by
  rcases h with rfl | rfl
  · by_cases h0 : (m : K) = 0 ∨ (r : K) = 0 ∨ (N : K) ^ d' = 0
    · refine ⟨0, ?_⟩
      rcases h0 with h | h | h <;> simp [h]
    · push Not at h0
      obtain ⟨a, b, c⟩ := h0
      refine ⟨1, ?_⟩
      push_cast
      rw [mul_pow]
      field_simp
  · exact ⟨0, by simp⟩

end Parts

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

theorem theta_value_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (n d N : ℕ) (La : GenLat E n) (w : (Fin n → LevQ Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F) (v : T.Fr), Good y → La.Unimod → La.TrivAt l.M → La.LevOK N l.M → (∀ q, InV T (io (w q))) → P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) → P.IsHomogeneous d → (∀ m, InV T (io (P.coeff m))) → (letI := io.toAlgebra; thLaValAt Xo c nab w La N P y.1 v) → InV T (((La.mIdx N (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw l) : ℕ) : T.Fr) * ((2 * NumberField.discr E * N : ℤ) : T.Fr) ^ d * v) := by
  intro E _ _ _ H Dw l Xo c _ nab hnab T io y n d N La w P v hy hU hT hL hw hP hd hc hv
  obtain ⟨T', iT, e, y', C, ⟨he, hval, φ, hφ, hmap⟩, hC, hrat⟩ :=
    exists_ext hnab.1 y hy (N ^ 2) (pow_pos hL.1.pos 2)
  letI := io.toAlgebra
  letI := (iT.comp io).toAlgebra
  obtain ⟨z, tp, F, hz, hg, ht, hF⟩ :=
    (GlobalTheory.RatData.exists_thetaVal_data E H Dw l Xo c T'.Fr y'.1).2 n La N hU hL hrat
  have key := GlobalTheory.HarmonicAny.map_shortValAt nab hnab La N hU hT hL P hP w 1 φ y.1 y'.1 hmap z tp F hz hg ht hF v hv
  have hφv : φ v = iT v := congrArg (fun g : T.Fr →+* T'.Fr => g v) hφ
  choose f hf using fun q i b => (GlobalTheory.RegularGerm.regular_germ E H Dw l Xo c hnab.1 T' _ y' C hC.1 (N ^ 2) _).1
    (GlobalTheory.ReachRegular.regular_of_reach E H Dw l Xo c hnab.1 T' _ y' C hC (N ^ 2) _
      (reach_of_isUUOver hL.1 (GlobalTheory.PlaceInt.sOf1 y') ((hz i).1 b)
        (root_pow_sq _ hL.2.1 _ (ht q b).1) (hF q i b)))
  have hb := fun q i => hv_bound nab hnab y' C (N ^ 2) n d _ (f q i) (hf q i) P hP hd
    (fun m => (inV_of_ext iT he hval).2 (hc m))
  have hcast := (GlobalTheory.PlaceInt.hv_linear E H Dw l Xo c hnab.1 nab hnab T'.Fr y'.1 n P).2.2 N
  haveI := GlobalTheory.ShortAtField.finite_levQ Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  haveI : CharZero T'.Fr := algebraRat.charZero _
  rw [← inV_of_ext iT he hval, map_mul, map_mul, map_pow, map_natCast, map_intCast, ← hφv, key]
  simp only [map_mul, map_inv₀, map_one, map_natCast, map_pow]
  have hcases : P.totalDegree = d ∨ (∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F T'.Fr (w q) *
      ∑ i, ∑ m ∈ P.support, algebraMap c.F T'.Fr (P.coeff m) *
        ∏ b, nab y'.1 ((N : ℤ) ^ 2) (F q i b) (colOf m b)) = 0 := by
    by_cases h0 : P = 0
    · right
      subst h0
      simp
    · exact Or.inl (hd.totalDegree h0)
  obtain ⟨ε, hε⟩ := scalar_cases (La.mIdx N (Dw.p + Dw.q)) (Nat.card (Fin n → LevQ Dw l)) N d P.totalDegree
    (NumberField.discr E) _ hcases
  rw [hε]
  refine Subring.mul_mem _ (natCast_mem _ ε) ?_
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Subring.sum_mem _ fun q _ => ?_
  rw [mul_left_comm, Finset.mul_sum]
  refine Subring.mul_mem _ ((inV_of_ext iT he hval).2 (hw q)) (Subring.sum_mem _ fun i _ => ?_)
  rw [hcast (F q i)]
  exact hb q i

end GlobalTheory.GoodThetaBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.XiTypeProof

theorem xiType : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), (∀ i j b, Faithful (rd i j b)) →
    (∀ i j b, ActRead (rd i j b)) → ρ.LevelOf D.nexp → XiType rd := by
  intro D ρ hρ rd hF hA hL i _ j b Q M hQ s h P _ _ a x hx
  unfold Formalism.MainNotions.IntegralHeckeForms.Fm0
  rw [Submodule.mem_iInf]
  intro u
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) :=
    GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D _ D.ntw ρ hρ i j b _ (fun _ h => isSplit_of_mem_admissibleConjugatePairPlaces h) (hQ.2.2.mono_left (admissibleConjugatePairPlaces_subset i Q M))
  have hu : ρ.eG i j b u ∈ (ρ.B i j b).G.P.H := (hL.U_eq i j b u).2 u.2
  obtain ⟨κ, hlift, hsupp, hser⟩ := GlobalTheory.T.thetaSeries_type_under_supported_lifts D _ _ (ρ.B i j b) (hρ.base i j b) (D.sp.V_sig _) _ (hρ.weil_base i j b) _ hu
  have hg := GlobalTheory.UnivGood.univOf_good D _ D.ntw ρ hρ D.nexp i Q M
  have hdet : detChar (Wc D j) ((univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M))) κ = 1 := by
    apply Multiplicative.toAdd.injective
    funext PP
    have := GlobalTheory.T.goodTwist_detChar_eq_one_of_supported_typePlaces D _ _ (ρ.B i j b) (hρ.base i j b) (D.sp.V_sig _) _ ⟨{PP.1}, _, _⟩ (hg.2 PP.1 PP.2)
      (hadm.mono (by simpa using PP.2)) _ κ hlift hsupp
    exact congrArg Multiplicative.toAdd this
  apply (hF i j b).injective
  funext g
  change rd i j b (D.nexp.actG i _ b u x) g = rd i j b (((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • x) g
  rw [hA i j b u κ hlift, map_smulₛₗ, Pi.smul_apply, hx]
  unfold Setup.xi
  rw [Base.xiCoef_apply, Base.xiCoef_apply, detChar_mul hg.delQ_real, hdet, mul_one]
  refine (hser _ hadm _ h P g).trans ?_
  rw [hL.psiU_eq i j b u hu, smul_eq_mul]
  rfl

end GlobalTheory.XiTypeProof
end

