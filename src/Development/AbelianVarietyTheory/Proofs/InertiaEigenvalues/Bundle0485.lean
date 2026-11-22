import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlWcbInjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Development
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0153
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0180
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0177
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0448

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulCocycle
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.HerrExtUnit

theorem exists_unit (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    let S := sit D.loc HW l (D.locA l) K s LL h
    let E : S.Comparison₂ := ((F l).E K s LL h).tie
    ∀ (e : S.W.DD S.W.one) (t : ↥S.W.one.L.T),
      S.W.N S.W.one = Submodule.span (LetA S.O S.n) {e} → S.W.φD S.W.one e = e →
      Submodule.span S.O {(t : S.W.one.V)} = S.W.one.L.T →
      ∃ u : (S.O)ˣ, ∀ a : S.O,
        E.jD S.W.one (a • e) = (1 : S.RW) ⊗ₜ[S.O] (((u : S.O) * a) • t) := by
  intro S E e t hN hφ ht
  obtain ⟨u, hu'⟩ : ∃ u : (S.O)ˣ, E.jD S.W.one e = (algebraMap S.O S.RW (u : S.O)) ⊗ₜ[S.O] t :=
    GlobalTheory.Cyc.UnitGen.main D HW F l K s LL h e t hN hφ ht
  refine ⟨u, fun a => ?_⟩
  rw [map_smul, hu', Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_smul, smul_smul, mul_comm]

theorem smul_cocycle (S : Sit) {T Tp : LocLat S.G S.Qp S.LL S.O} (ι : LatHom T.L Tp.L) (x : T.V)
    (g : S.G) (et : Tp.V) (hx : ι.f x = Tp.ρ g et - et) (b : S.O) :
    ι.f (b • x) = Tp.ρ g (b • et) - b • et := by
  rw [← algebraMap_smul S.LL b x, ← algebraMap_smul S.LL b et, map_smul, map_smul, hx, smul_sub]

theorem smul_proj (S : Sit) {Tp Z : LocLat S.G S.Qp S.LL S.O} (π : LatHom Tp.L Z.L)
    (et : Tp.V) (b : S.O) : b • π.f et = π.f (b • et) := by
  rw [← algebraMap_smul S.LL b et, map_smul, algebraMap_smul]

theorem over_Ks (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    Formalism.MainNotions.ElementDenominator.coreHerrExt (sit D.loc HW l (D.locA l) K s LL h).W := by
  intro T Tp ι π _ _ c hc hE e he
  obtain ⟨hS, et, het, hgen, hcoc⟩ := hE
  obtain ⟨u, hu⟩ := exists_unit D HW F l K s LL h e ⟨π.f et, π.T_le _ het⟩ he.1 he.2.1 hgen
  refine ⟨u, fun x a hx y z hyz h1 h2 => ?_⟩
  have key := GlobalTheory.Cyc.dict_ext_Ks D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    T Tp _ ι π hS (sit D.loc HW l (D.locA l) K s LL h).W.one_triv
    ((u.1 * a) • ⟨et, het⟩) ((u.1 * a) • ⟨π.f et, π.T_le _ het⟩) x
    (smul_proj _ π et _) (by rw [hx]; exact hu a) ⟨(y, z), hyz⟩ h1 h2
    ((u.1 * a) • ⟨_, resFun_Z1T T _ c hc⟩)
    (fun g => smul_cocycle _ ι _ g et (hcoc g) _)
  exact key.trans (Submodule.Quotient.mk_smul _ _ _)

theorem over_K (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) :
    Formalism.MainNotions.ElementDenominator.coreHerrExtΔ (sit D.loc HW l (D.locA l) K s LL h).W := by
  intro _ hp T Tp ι π _ _ c hc hE e he
  obtain ⟨hS, et, het, hgen, hcoc⟩ := hE
  obtain ⟨u, hu⟩ := exists_unit D HW F l K s LL h e ⟨π.f et, π.T_le _ het⟩ he.1 he.2.1 hgen
  refine ⟨u, fun x a hδ hx y z hyz h1 h2 => ?_⟩
  have key := GlobalTheory.ExtDict.dict_K D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    (fun h2 => absurd h2 hp) T Tp _ ι π hS (sit D.loc HW l (D.locA l) K s LL h).W.one_triv
    ((u.1 * a) • ⟨et, het⟩) ((u.1 * a) • ⟨π.f et, π.T_le _ het⟩) x
    (smul_proj _ π et _) (by rw [hx]; exact hu a) hδ ⟨(y, z), hyz⟩ h1 h2
    ((u.1 * a) • ⟨c, hc⟩)
    (fun g => smul_cocycle _ ι _ g et (hcoc g) _)
  exact key.trans (Submodule.Quotient.mk_smul _ _ _)

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.HerrComplexNaturality.HerrExtensionUpToUnit D HW F :=
  fun D HW F l _ K s LL h => ⟨over_Ks D HW F l K s LL h, over_K D HW F l K s LL h⟩

end GlobalTheory.HerrExtUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiFil

variable {l : ℕ} [Fact l.Prime]

theorem mem_FilD_zero_iff (x : Per.BdR l) :
    x ∈ Per.FilD l 0 ↔ ∃ z : Per.BdRp l, x = algebraMap (Per.BdRp l) (Per.BdR l) z := by
  have h := GlobalTheory.BdRQuot.mem_FilD_nat (l := l) 0 x
  rw [Nat.cast_zero] at h
  rw [h]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, GlobalTheory.BdRQuot.mem_filtration_zero z, rfl⟩

theorem mul_mem_FilD_of_zero {x y : Per.BdR l} {n : ℤ} (hx : x ∈ Per.FilD l 0) (hy : y ∈ Per.FilD l n) :
    x * y ∈ Per.FilD l n := by
  obtain ⟨z, rfl⟩ := (mem_FilD_zero_iff x).1 hx
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ z hy

theorem mul_mem_FilD_neg {x y : Per.BdR l} {m : ℕ} (hx : x ∈ Per.FilD l m) (hy : y ∈ Per.FilD l (-(m : ℤ))) :
    x * y ∈ Per.FilD l 0 := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.BdRField.exists_isEps l
  obtain ⟨w, rfl⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he _ x).1 hx
  obtain ⟨w', rfl⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he _ y).1 hy
  rw [mul_mul_mul_comm, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_mul,
    ← map_mul]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero _

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def filO (C : GlobalTheory.MemLoc.Core l) (n : ℤ) : Submodule O (OB l O) :=
  Submodule.span O {x | ∃ β : Per.Bcris l, C.ι β ∈ Per.FilD l n ∧ x = (1 : O) ⊗ₜ[ℤ_[l]] β}

variable {O} {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

def filT (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) (n : ℤ) : Submodule O (TW (OB l O) T) :=
  Submodule.span O {w | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l n ∧
    w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x}

theorem smul_mem_filT {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {a b c : ℤ}
    (hmul : ∀ β β' : Per.Bcris l, C.ι β ∈ Per.FilD l a → C.ι β' ∈ Per.FilD l b → C.ι (β * β') ∈ Per.FilD l c)
    {r : OB l O} (hr : r ∈ filO O C a) {v : TW (OB l O) T} (hv : v ∈ filT C T b) : r • v ∈ filT C T c := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨β, hβ, rfl⟩ := hr
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨β', x, hβ', rfl⟩ := hv
      rw [smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      exact Submodule.subset_span ⟨β * β', x, hmul β β' hβ hβ', rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add v v' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | smul o v _ h => rw [smul_comm]; exact Submodule.smul_mem _ o h
  | zero => rw [zero_smul]; exact zero_mem _
  | add r r' _ _ h h' => rw [add_smul]; exact add_mem h h'
  | smul o r _ h => rw [smul_assoc]; exact Submodule.smul_mem _ o h

theorem smul_mem_filT_of_zero {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {n : ℤ} {r : OB l O}
    (hr : r ∈ filO O C 0) {v : TW (OB l O) T} (hv : v ∈ filT C T n) : r • v ∈ filT C T n :=
  smul_mem_filT (fun β β' h h' => by rw [map_mul]; exact mul_mem_FilD_of_zero h h') hr hv

theorem smul_mem_filT_neg {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {m : ℕ} {r : OB l O}
    (hr : r ∈ filO O C m) {v : TW (OB l O) T} (hv : v ∈ filT C T (-(m : ℤ))) : r • v ∈ filT C T 0 :=
  smul_mem_filT (fun β β' h h' => by rw [map_mul]; exact mul_mem_FilD_neg h h') hr hv

end GlobalTheory.BKGal.XiFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanMulMem
section
namespace GlobalTheory.SpanMulInertiaEigenvalues

open NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem span_mul_mem {a b : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}
    (ha : a ∈ Formalism.L2.SG.LocVol.OEv v) (hb : b ∈ Formalism.L2.SG.LocVol.OEv v) :
    a * b ∈ Formalism.L2.SG.LocVol.OEv v := by
  unfold Formalism.L2.SG.LocVol.OEv at *
  rw [SetLike.mem_coe] at *
  set S := (fun x : 𝓞 E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (x : E)) '' Set.univ
    with hS
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    refine ⟨x * y, Set.mem_univ _, ?_⟩
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR _ (algebraMap (𝓞 E) E (x * y)) = _
    rw [map_mul, map_mul]
  have key : ∀ x ∈ S, ∀ y ∈ Submodule.span (v.adicCompletionIntegers F) S,
      x * y ∈ Submodule.span (v.adicCompletionIntegers F) S := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (hSmul x hx y hy)
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  induction ha using Submodule.span_induction with
  | mem x hx => exact key x hx b hb
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {a b : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}, a ∈ Formalism.L2.SG.LocVol.OEv v → b ∈ Formalism.L2.SG.LocVol.OEv v → a * b ∈ Formalism.L2.SG.LocVol.OEv v :=
  fun v _ _ ha hb => span_mul_mem v ha hb

end GlobalTheory.SpanMulInertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictnessOfTied
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

namespace GlobalTheory.FontaineExtensionCriteria

open GlobalTheory.Per.FontaineBound in

theorem fontCore_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K : FinExt l) : LocalSituation.fontCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A
  have : FiniteDimensional ℚ_[l] LL := hO.2.1
  have hd := ddR_finite_le (P.PD K) (isField_of_tied T) A.ρ
  refine ⟨?_, hd, fun hc => ?_⟩
  · have := isDomain_cris (P.PD K) (isField_of_tied T)
    have := (P.PD K).finK₀
    refine finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.T.ratio_invariant_in_K0 l P AI T K b' b hb fun g hg => ?_) A.ρ
    have h1 := h ⟨g, hg⟩
    rw [P.PD_actB, P.PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  · refine (GlobalTheory.Per.CrisDR.abstract_cmp (P.PD K) A.ρ
      (fun m x hx b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m x hx b ?_) hd.1 hd.2 hc).1
    simpa only [P.PD_ι] using hb

theorem strictness_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) :
    GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P :=
  (GlobalTheory.DeRhamCompare.strict_iff P).1 (GlobalTheory.DRFil.deRhamComparison l P AI ⟨T⟩).2.2.2.2.2.1

theorem extCrys_of_tied : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    Nonempty (LocTied l P AI) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrys P :=
  fun P _ ⟨T⟩ => GlobalTheory.CrysExt.extCrys P (fontCore_of_tied T) (strictness_of_tied T)

end GlobalTheory.FontaineExtensionCriteria
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSettingGroupActionCompat
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.SESExact

theorem homW_exact_middle : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), ∀ v : κ → OW l O, homW t ϖ H v = 0 → ∃ w, homW t ϖ F w = v := by
  intro l _ a _ e _ O K _ _ _ _ _ _ _ _ _ t ϖ G _ _ ι κ μ _ _ _ _ _ _ P₀ P₁ P₂ T₀ T₁ T₂ I₀ I₁ I₂ f g F H hS hF hH v hv
  obtain ⟨-, -, hOnto, hker, hsat⟩ := hS
  set f₁ := (f.f.restrictScalars O).restrict f.T_le with hf₁
  set g₁ := (g.f.restrictScalars O).restrict g.T_le with hg₁
  have hgs : Function.Surjective g₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hOnto y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hex : Function.Exact f₁ g₁ := by
    rintro ⟨y, hy⟩
    constructor
    · intro h0
      have h0' : g.f y = 0 := congrArg Subtype.val h0
      obtain ⟨z, hz⟩ := (hker y).1 h0'
      have hzT : z ∈ T₀.L.T := hsat z (hz ▸ hy)
      exact ⟨⟨z, hzT⟩, Subtype.ext hz⟩
    · rintro ⟨⟨z, hzT⟩, hz⟩
      apply Subtype.ext
      have hz' : f.f z = y := congrArg Subtype.val hz
      exact (hker y).2 ⟨z, hz'⟩
  have hT := lTensor_exact (OW l O) hex hgs
  have h1 : latW g (I₁.j v) = 0 := by
    rw [← hH v, hv, map_zero]
  obtain ⟨z, hz⟩ := (hT (I₁.j v)).1 h1
  refine ⟨I₀.j.symm z, I₁.j.injective ?_⟩
  rw [hF, LinearEquiv.apply_symm_apply]
  exact hz

end GlobalTheory.BKReal.SESExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorOneInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TensorOneInj

theorem bcris_nontrivial (l : ℕ) [Fact l.Prime] : Nontrivial (Per.Bcris l) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  have : Nontrivial (Per.BdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.nontrivial
  exact C.ι.domain_nontrivial

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap ℤ_[l] (Per.Bcris l)) := by
  have := bcris_nontrivial l
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (algebraMap ℤ_[l] (Per.Bcris l) (PadicInt.unitCoeff h0 : ℤ_[l])) :=
    (PadicInt.unitCoeff h0).isUnit.map _
  exact (hu.mul ((GlobalTheory.MemLoc.isUnit_l_Bcris l).pow _)).ne_zero hx

theorem algebraMap_OB_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] : Function.Injective (algebraMap O (OB l O)) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ_[l] (Per.Bcris l)) (algebraMap_injective l)
  have e : ⇑(algebraMap O (OB l O)) =
      (LinearMap.lTensor O (Algebra.linearMap ℤ_[l] (Per.Bcris l))) ∘ (TensorProduct.rid ℤ_[l] O).symm := by
    funext o
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [e]
  exact h.comp (TensorProduct.rid ℤ_[l] O).symm.injective

theorem tensor_one_injective : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O),
    Function.Injective fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ O K _ _ _ _ _ _ _ _ G _ _ T
  haveI : Module.Free O ↥T.L.T := T.L.free
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T)
    (Algebra.linearMap O (OB l O)) (algebraMap_OB_injective l O)
  have e : (fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x) =
      (LinearMap.rTensor (↥T.L.T) (Algebra.linearMap O (OB l O))) ∘ (TensorProduct.lid O ↥T.L.T).symm := by
    funext x
    simp [Algebra.TensorProduct.one_def]
  rw [e]
  exact h.comp (TensorProduct.lid O ↥T.L.T).symm.injective

end GlobalTheory.TensorOneInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGoodRowPointGoodStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_goodRow_point_good : ∀ (D : D7), SumRepresentations.Conclusion42 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (x : D.nd.X i), D.nd.goodRow σ → thetaOf D.nd D.naut i σ P → D.naut.ptV i P = some x → x ∈ ZgoodN D.nd D.naut i ∧ AtM D.nd D.naut i σ := by
  first | exact @GlobalTheory.GoodLiftPoint.good_of_lift | exact GlobalTheory.GoodLiftPoint.good_of_lift | (intros; apply GlobalTheory.GoodLiftPoint.good_of_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLocusDecomposesOverCoefRingOfChebotarevStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLocusDecomposesOverCoefRing_of_chebotarev : GlobalTheory.TwSys.Cheb → ∀ (D : D7), GlobalTheory.BlockComplement.GaloisRepsCusp D → ∀ i : D.nd.Loc, ZDecomp D.nd i := by
  first | exact @GlobalTheory.ZDecompAt.zDecomp_of_cheb | exact GlobalTheory.ZDecompAt.zDecomp_of_cheb | (intros; apply GlobalTheory.ZDecompAt.zDecomp_of_cheb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiedIsCrysDual
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedDual

theorem tied_isCrys_dual : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ.dual := by
  intro l _ P AI T hreg K LL V _ _ _ _ _ ρ hρ
  have := LL.2
  have : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have e : ∀ (g : ↥(GK K)) z, (P.PD K).actB g z = P.actQ g z := fun g z => P.PD_actB K g z
  have hf : GlobalTheory.RegularRing.FracInv (P.PD K) := by
    intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [e, e] at h1
    rw [mul_comm, h1, mul_comm]
  have hu : GlobalTheory.RegularRing.LineUnit (P.PD K) := by
    intro b hb h
    refine hreg K b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    exact ⟨x, by rw [← e ⟨g, hg⟩, hx, Algebra.smul_def]⟩
  exact GlobalTheory.RegularRing.dualCrys (P.PD K) ↥LL.1 hf hu V ρ hρ

end GlobalTheory.Per.TiedDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltOrthOfUntiltOrthStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sh_le_sh_int_sum_of_orthogonal : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (m : Fin h → Fl l), (∀ i j, ‖sh (m i)‖ < l * ‖sh (m j)‖) →
    (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖sh (m j)‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * sh (m i)‖) →
    ∀ (c : Fin h → ℤ) (j : Fin h), ¬ (l : ℤ) ∣ c j → ‖sh (m j)‖ ≤ ‖sh (∑ i, (c i : Fl l) * m i)‖ := by
  first | exact @GlobalTheory.tilt_orth_of_untilt_orth | exact GlobalTheory.tilt_orth_of_untilt_orth | (intros; apply GlobalTheory.tilt_orth_of_untilt_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUniformizerPowEqMulUnitStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_uniformizer_pow_eq_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ϖ : OCb l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    ∃ x : OCb l, IsUnit x ∧ bk.flat ^ bk.Ep.natDegree = ϖ * x := by
  first | (exact @GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit) | (exact GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit) | (intros; apply GlobalTheory.TiltDiv.flat_pow_natDegree_eq_mul_unit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltedSeriesRowSubUntiltTruncatedAdditiveRow
section
noncomputable section

open Formalism.Per GlobalTheory.PSer Finset
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem row_lam_sub_untilt_rowT : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CharP F l]
    [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (h : ℕ) (m x : Fin h → Fl l) (ϖ : F) (K : ℕ) (τ : Fin h → ℝ) (r : Fin h), 1 ≤ h → tsh ϖ = l →
      (∀ j, ‖sh (x j)‖ < 1) →
      (∀ (j : Fin h) (n : ℤ), ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r ∧
        ((K : ℤ) < |n| → ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r / l)) →
      ‖∑ j, sh (m j) * lam h r (x j) - tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
  intro l _ F _ _ _ _ ι tsh hn hs hsurj h m x ϖ K τ r hh hϖ hx hT
  have hid : ∀ j n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) =
      sh (m j) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((r : ℕ) : ℤ)) (x j))) := by
    intro j n
    simp only [GlobalTheory.PMonE.term, map_mul, map_zpow₀, hϖ, hs]
    rw [← GlobalTheory.T.ringHom_tilt_map_tiltFrobeniusIntegerPower l F ι, hs]
    rw [show ((r : ℤ) + n * h) = n * h + ((r : ℕ) : ℤ) by push_cast; ring]
    ring
  have hR : 0 ≤ τ r := (norm_nonneg _).trans (hT r 0).1
  have hR' : 0 ≤ ‖(l : ℂ_[l])‖ * τ r := mul_nonneg (norm_nonneg _) hR
  have hlb : τ r / l = ‖(l : ℂ_[l])‖ * τ r := by rw [Laws.norm_l, div_eq_inv_mul]
  have htail : ∀ j, ‖sh (m j) * lam h r (x j) -
      ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
    intro j
    have hsum : Summable (fun n => tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) := by
      simp only [hid]; exact (Laws.summable_lam hh r (hx j)).mul_left _
    have hlam : sh (m j) * lam h r (x j) =
        ∑' n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) := by
      simp only [hid, lam]; rw [tsum_mul_left]
    rw [hlam, ← hsum.sum_add_tsum_compl (s := Icc (-(K : ℤ)) K), add_sub_cancel_left]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hR' fun ⟨n, hmem⟩ => ?_
    rw [← hlb]
    show ‖tsh _‖ ≤ _
    rw [hn]
    apply (hT j n).2
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hmem
    rw [lt_abs]; omega
  have hfin : ‖∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
      tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖ ≤ ‖(l : ℂ_[l])‖ * τ r := by
    have := GlobalTheory.T.norm_untilt_extension_finset_sum_sub_le l F ι tsh hn hs hsurj (Fin h × ℤ) (univ ×ˢ Icc (-(K : ℤ)) K)
      (fun a => GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r a.1 a.2) (τ r) hR
      (fun a _ => (hT a.1 a.2).1)
    simp only [Finset.sum_product] at this
    rw [norm_sub_rev]
    simpa [GlobalTheory.PMonE.rowT] using this
  calc _ = ‖∑ j, (sh (m j) * lam h r (x j) -
        ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) +
      (∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
        tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r))‖ := by
        rw [Finset.sum_sub_distrib]; congr 1; abel
    _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR' fun j _ => htail j) hfin

end GlobalTheory.PSer

end
end

