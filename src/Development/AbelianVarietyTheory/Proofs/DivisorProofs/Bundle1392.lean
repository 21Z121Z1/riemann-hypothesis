import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionInvariantRationalTarget
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPureTensorsProductMeasureFiniteAdelic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0008
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTensorLatticeComponentIntegral
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem piW_smul_incl (v : Pl F) (t : E →ₐ[F] Fv F v) (a : AF F) (e : E) :
    piW t (a • inclR (F := F) (AF F) e) = evFin F v a * t e := by
  simp [piW, inclR, compFin, TensorProduct.smul_tmul', splitProj_tmul]

theorem comp_mem_splitLat (v : Pl F) (t : E →ₐ[F] Fv F v) {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (hx : x ∈ L) : (fun i => t (x i)) ∈ splitLat t L := by
  refine ⟨_, tmul_mem_latLoc (one_mem _) hx, funext fun i => ?_⟩
  simp [splitVec, splitProj_tmul]

end GlobalTheory.LatInt

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem map_piW_gen (v : Pl F) (t : E →ₐ[F] Fv F v) (a : AF F) (x : Fin n → E) (y : Fin d → E) :
    (a • incM F (Matrix.vecMulVec x y)).map (piW t) =
      evFin F v a • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (y j)) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.smul_apply, incM, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [piW_smul_incl, map_mul]

theorem latAtV_comp_integral {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)) (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) :
    ∀ γ ∈ latAtV X W v, ∀ i j,
      ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) i j ∈ v.adicCompletionIntegers F := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, x, hx, y, hy, rfl⟩ := hz
    have hx' := (hb.mem_iff).1 (comp_mem_splitLat v t hx)
    have hy' := (hc.mem_iff).1 (comp_mem_splitLat v t hy)
    intro i j
    rw [map_piW_gen, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    exact mul_mem ha (mul_mem (hx' i) (hy' j))
  | zero => intro i j; simp
  | add γ δ _ _ hγ hδ =>
    intro i j
    rw [Matrix.map_add (piW t) (map_add _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    exact add_mem (hγ i j) (hδ i j)
  | neg γ _ hγ =>
    intro i j
    rw [Matrix.map_neg (piW t) (map_neg _), Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
    exact neg_mem (hγ i j)

end GlobalTheory.LatInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementSecondPolynomial
section
noncomputable section

namespace GlobalTheory.SplitTransfer

section Abstract

open Formalism.UG GlobalTheory.PRep

theorem heckeVec_indicator {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {x : V} (hx : x ∈ fixed ρ K) {S : Set G} (hm : ∀ g ∈ S, ∀ k ∈ K, g * k ∈ S) (R : Finset ι)
    (g : ι → G) (hR : ∀ i ∈ R, g i ∈ S) (hR' : ∀ y ∈ S, ∃! i, i ∈ R ∧ (g i)⁻¹ * y ∈ K) :
    GlobalTheory.LFun.heckeVec ρ K (Set.indicator S 1) x = ∑ i ∈ R, ρ (g i) x := by
  classical
  have hinj : Set.InjOn (fun i : ι => (g i : G ⧸ K)) R := fun γ hγ δ hδ e =>
    (hR' _ (hR δ hδ)).unique ⟨hγ, QuotientGroup.eq.1 e⟩ ⟨hδ, by simp⟩
  rw [GlobalTheory.LFun.heckeVec, finsum_eq_sum_of_support_subset (s := R.image fun i : ι => (g i : G ⧸ K)),
    Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (g γ)
    rw [hk, Set.indicator_of_mem (hm _ (hR γ hγ) k k.2), map_mul, Module.End.mul_apply,
      GlobalTheory.LGrp.mem_fixed.1 hx _ k.2]
    simp
  · intro c hc
    have : c.out ∈ S := by
      by_contra h0
      exact hc (by simp [h0])
    obtain ⟨γ, ⟨h1, h2⟩, -⟩ := hR' _ this
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, h1, (QuotientGroup.eq.2 h2).trans c.out_eq'⟩)

end Abstract

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.InertHeckeEigen Formalism.UG GlobalTheory.PRep GlobalTheory.DefU in

theorem heckeVec_eq_of_isCompAlong {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {U : Submodule ℂ (UA L n → ℂ)} (hU : IsAutRepU U) (w : HeightOneSpectrum (𝓞 L)) {H X : Type} [Group H]
    [AddCommGroup X] [Module ℂ X] {K : Subgroup H} (hK : IsCommensurated K) (p : locU n w →* H)
    (hp : Function.Surjective p) (σ : Representation ℂ H X) (hcomp : IsCompAlong U (locU n w) p σ) {h : H → ℂ}
    (hh : h ∈ Hecke ℂ K) {lam : ℂ} (hsat : ∀ v ∈ fixed σ K, v ≠ 0 → GlobalTheory.LFun.heckeVec σ K h v = lam • v)
    {φ : UA L n → ℂ} (hφ : φ ∈ U) (hfix : ∀ x : locU n w, p x ∈ K → RU L n x.val φ = φ) :
    GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) (K.comap p) (fun x => h (p x)) φ = lam • φ := by
  have hfin : {c : locU n w ⧸ K.comap p | h (p c.out) ≠ 0}.Finite :=
    finite_support_comp p hp hh.1 (Formalism.UG.P.finite_support_cosets hK hh.2)
  have hS : ∀ c : locU n w ⧸ K.comap p, (fun x => h (p x)) c.out ≠ 0 → c ∈ hfin.toFinset :=
    fun c hc => hfin.mem_toFinset.2 hc
  let T : (UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    ∑ c ∈ hfin.toFinset, h (p c.out) • (RU L n) (c.out : UA L n)
  have hT : ∀ x, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) (K.comap p) (fun x => h (p x)) x
      = T x := fun x => by
    rw [heckeVec_eq_sum _ _ _ _ hS x]
    simp [T, LinearMap.sum_apply]
  let Z : Submodule ℂ (UA L n → ℂ) :=
    fixed ((RU L n).comp (locU n w).subtype) (K.comap p) ⊓ LinearMap.ker (T - lam • LinearMap.id)
  have hZ' : ∀ x, x ∈ Z ↔ (∀ k ∈ K.comap p, RU L n (k : UA L n) x = x) ∧ T x = lam • x := fun x => by
    simp only [Z, Submodule.mem_inf, GlobalTheory.LGrp.mem_fixed, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  let π : AutSub L n := ⟨U, hU⟩
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hcomp
  have hirr : Representation.IsIrreducible (σ.comp p) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints L n w
  have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA L n) (locU n w) π.V X X π.rep (locU n w).subtype (σ.comp p) (σ.comp p)
    π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype) → X →ₗ[ℂ] (UA L n → ℂ) :=
    fun i => U.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.comp p) g u) = (RU L n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining (σ.comp p) (π.rep.comp (locU n w).subtype) i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype),
        LinearMap.range i.toLinearMap).map U.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this
  have hZ : ∀ i v, (∀ k ∈ (K.comap p : Set (locU n w)), (σ.comp p) k v = v) → fi i v ∈ Z := by
    intro i v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]; exact Z.zero_mem
    have hvK : v ∈ fixed σ K := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
      obtain ⟨x, rfl⟩ := hp k
      exact hv x hk
    refine (hZ' _).2 ⟨fun k hk => (hfi i k v).symm.trans (congrArg (fi i) (hv k hk)), ?_⟩
    have e2 := heckeVec_comp_surj p hp hh.1 σ hvK
    rw [heckeVec_eq_sum _ _ _ _ hS] at e2
    rw [hsat v hvK hv0] at e2
    rw [← hT (fi i v), heckeVec_eq_sum _ _ _ _ hS]
    calc _ = fi i (∑ c ∈ hfin.toFinset, h (p c.out) • (σ.comp p) c.out v) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_smul, hfi]
      _ = lam • fi i v := by rw [e2, map_smul]
  have hZK : ∀ z ∈ Z, ∀ k ∈ (K.comap p : Set (locU n w)), (RU L n).comp (locU n w).subtype k z = z :=
    fun z hz k hk => ((hZ' z).1 hz).1 k hk
  have hφZ := mem_of_mem_iSup ((RU L n).comp (locU n w).subtype) (σ.comp p) hirr fi hfi _ Z hZ hZK φ
    (fun k hk => hfix k hk) hmem
  rw [hT]
  exact ((hZ' φ).1 hφZ).2

end GlobalTheory.SplitTransfer

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTransfer

theorem heckeVec_divInd {D : D7} [IsCMField D.host.E] {V : HSp D}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {j : UA D.host.E V.rank ≃ₜ* GA D V} {h₀ : GA D V} (hT : IsTransfer V θ j h₀)
    {P : HeightOneSpectrum (𝓞 D.host.E)} {φ : UA D.host.E V.rank → ℂ}
    (hφ : ∀ x ∈ KP V.rank P, RU D.host.E V.rank x φ = φ) {d : List ℤ} {R : Finset (GA D V)}
    (hR : GlobalTheory.Hk3.SphOp V P d R) :
    GlobalTheory.LFun.heckeVec ((RU D.host.E V.rank).comp (locU V.rank P).subtype)
      ((GlobalTheory.LFun.KGL P V.rank).comap ((cLoc P).comp (locU V.rank P).subtype))
      (fun x => divInd (Ov D.host.E P) d (((cLoc P).comp (locU V.rank P).subtype) x)) φ =
      ∑ γ ∈ R, RU D.host.E V.rank ((cj j h₀).symm γ) φ := by
  classical
  obtain ⟨h1, h2⟩ := hT.2.2.2.2.2.2.2 P d R hR
  let g : GA D V → locU V.rank P := fun γ =>
    if h : (cj j h₀).symm γ ∈ locU V.rank P then ⟨_, h⟩ else 1
  have hg : ∀ γ ∈ R, (g γ : UA D.host.E V.rank) = (cj j h₀).symm γ := fun γ hγ => by
    simp only [g, dif_pos (h1 γ hγ).1]
  have e : (fun x : locU V.rank P => divInd (Ov D.host.E P) d (((cLoc P).comp (locU V.rank P).subtype) x)) =
      Set.indicator {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)} 1 := by
    funext x
    by_cases hx : HasDiv (Ov D.host.E P) d (cLoc P x.val)
    · rw [Set.indicator_of_mem (s := {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)}) hx]
      exact Set.indicator_of_mem (s := {g | HasDiv (Ov D.host.E P) d g}) hx _
    · rw [Set.indicator_of_notMem (s := {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)}) hx]
      exact Set.indicator_of_notMem (s := {g | HasDiv (Ov D.host.E P) d g}) hx _
  rw [e, heckeVec_indicator (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hφ k.val ⟨k.2, hk⟩) ?_ R g ?_ ?_]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [← hg γ hγ]
    rfl
  · intro x hx k hk
    have := GlobalTheory.SphGal.hasDiv_mul_mul hx (one_mem _) hk
    rw [one_mul] at this
    change HasDiv _ d (cLoc P (x.val * k.val))
    rw [map_mul]
    exact this
  · intro γ hγ
    change HasDiv _ d (cLoc P (g γ).val)
    rw [hg γ hγ]
    exact (h1 γ hγ).2
  · intro y hy
    obtain ⟨γ, ⟨a1, a2⟩, a3⟩ := h2 y.val y.2 hy
    refine ⟨γ, ⟨a1, ?_⟩, fun δ hδ => a3 δ ⟨hδ.1, ?_⟩⟩
    · change cLoc P ((g γ).val⁻¹ * y.val) ∈ GlobalTheory.LFun.KGL P V.rank
      rw [hg γ a1]
      exact a2.2
    · rw [← hg δ hδ.1]
      exact ⟨((g δ)⁻¹ * y).2, hδ.2⟩

end GlobalTheory.SplitTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def twistSpan (ν β : kˣ →* ℂˣ) : Submodule ℂ (Matrix A D k → ℂ) :=
  Submodule.span ℂ {z | ∃ (g : GL A k) (Ψ : Matrix A D k → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧
    z = omA ν β g 1 Ψ - Ψ}

def lowRank (r : ℕ) : Submodule ℂ (Matrix A D k → ℂ) where
  carrier := {Φ | Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0}
  add_mem' hΦ hΨ := ⟨add_mem hΦ.1 hΨ.1, fun Y hY => by simp [hΦ.2 Y hY, hΨ.2 Y hY]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ hΦ := ⟨Submodule.smul_mem _ c hΦ.1, fun Y hY => by simp [hΦ.2 Y hY]⟩

theorem mem_lowRank {r : ℕ} {Φ : Matrix A D k → ℂ} :
    Φ ∈ lowRank r ↔ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0 := Iff.rfl

theorem omA_one_apply (ν β : kˣ →* ℂˣ) (g : GL A k) (Φ : Matrix A D k → ℂ) (X : Matrix A D k) :
    omA ν β g 1 Φ X = (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * apow (gdet g) (-(Fintype.card D : ℂ) / 2) *
      Φ ((g⁻¹).val * X) := by
  simp [omA, invT_val]

theorem sub_mem_twistSpan (ν β : kˣ →* ℂˣ) (g : GL A k) {Ψ : Matrix A D k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix A D k)) : omA ν β g 1 Ψ - Ψ ∈ twistSpan ν β :=
  Submodule.subset_span ⟨g, Ψ, hΨ, rfl⟩

def box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : Set (Matrix A D k) :=
  {X | ∀ i j, valuation k (X i j - C i j) ≤ valuation k ((ϖ ^ e i : kˣ) : k)}

def boxFn (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : Matrix A D k → ℂ := (box ϖ C e).indicator 1

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in

theorem box_eq_preimage (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    box ϖ C e = (fun X : Matrix A D k => Matrix.of fun i j => (((ϖ ^ e i)⁻¹ : kˣ) : k) * (X i j - C i j)) ⁻¹'
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  ext X
  simp only [box, Set.mem_setOf_eq, Set.mem_preimage, of_apply, Valuation.mem_integer_iff, map_mul]
  refine forall₂_congr fun i j => ?_
  have h0 : 0 < valuation k ((ϖ ^ e i : kˣ) : k) := zero_lt_iff.2 (by simp)
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in

theorem box_eq_image (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    box ϖ C e = (fun Y : Matrix A D k => Matrix.of fun i j => C i j + ((ϖ ^ e i : kˣ) : k) * Y i j) ''
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  rw [box_eq_preimage]
  ext X
  constructor
  · intro hX
    refine ⟨_, hX, ?_⟩
    ext i j
    simp [← mul_assoc]
  · rintro ⟨Y, hY, rfl⟩
    simpa [← mul_assoc] using hY

omit [DecidableEq A] [DecidableEq D] in

theorem isCompact_box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : IsCompact (box ϖ C e) := by
  rw [box_eq_image]
  exact isCompact_intMatrix.image (by fun_prop)

omit [DecidableEq A] [DecidableEq D] in

theorem isClopen_box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : IsClopen (box ϖ C e) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : T2Space (Matrix A D k) := inferInstanceAs (T2Space (A → D → k))
  refine ⟨(isCompact_box ϖ C e).isClosed, ?_⟩
  rw [box_eq_preimage]
  exact isOpen_intMatrix.preimage (by fun_prop)

omit [DecidableEq A] [DecidableEq D] in

theorem boxFn_mem_SB (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    boxFn ϖ C e ∈ GlobalTheory.WeilM.SB (Matrix A D k) :=
  ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) (isClopen_box ϖ C e)).isLocallyConstant,
    HasCompactSupport.intro (isCompact_box ϖ C e) fun _ hx => Set.indicator_of_notMem hx _⟩

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in

theorem box_eq_of_mem {ϖ : kˣ} {C X : Matrix A D k} {e : A → ℕ} (hX : X ∈ box ϖ C e) : box ϖ X e = box ϖ C e := by
  ext Y
  refine ⟨fun hY i j => ?_, fun hY i j => ?_⟩
  · rw [show Y i j - C i j = (Y i j - X i j) + (X i j - C i j) by ring]
    exact Valuation.map_add_le _ (hY i j) (hX i j)
  · rw [show Y i j - X i j = (Y i j - C i j) - (X i j - C i j) by ring]
    exact Valuation.map_sub_le _ (hY i j) (hX i j)

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in

theorem boxFn_eq_of_mem {ϖ : kˣ} {C X : Matrix A D k} {e : A → ℕ} (hX : X ∈ box ϖ C e) :
    boxFn ϖ X e = boxFn ϖ C e := by
  rw [boxFn, boxFn, box_eq_of_mem hX]

end GlobalTheory.RankCoinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystemStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symbols_of_evaluated_columns_hermitianMultSystem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → ∀ l : Fin S.N → E, (∀ (a : Fin (S.T - S.D)) (α : MonoDeg (Fin S.D) a) (p : Fin δ), ∃ h : word Φ.mul (fun q k => join s l ((col (ix (⟨a, α⟩, p))).β q, k)) (Φ.ι (col (ix (⟨a, α⟩, p))).x) ∈ Φ.U a, ∀ α' p', Φ.sym a ⟨_, h⟩ (α', p') = if α'.1 = α.1 then (∑ k, l k * Φ.y p' k) ^ (S.T - a) * Φ.res (Φ.ι (m p)) p' else 0) ∧ ∀ k, k ∉ Set.range ix → (col k).j = S.D → word Φ.mul (fun q j => join s l ((col k).β q, j)) (Φ.ι (col k).x) ∈ Φ.U (S.T - S.D) := by
  first | exact @GlobalTheory.HSShort.symbols_of_columns | exact GlobalTheory.HSShort.symbols_of_columns | (intros; apply GlobalTheory.HSShort.symbols_of_columns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionInvariantRationalTargetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDistribution_invariant_rationalTarget : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∀ (of oi : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of → IsInfWeil ψ θ S T oi → ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → of (1, γ') (oi (1, γ') f) 0 = f 0 := by
  first | exact @GlobalTheory.RatAut.automorphy_target | exact GlobalTheory.RatAut.automorphy_target | (intros; apply GlobalTheory.RatAut.automorphy_target <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotFilTotSymKer
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem totFil_totSym_ker : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), ∀ a < X.T - X.D, totFil X s (a + 1) ≤ totFil X s a ∧ ∀ x : totFil X s a, totSym Co a x = 0 ↔ x.1 ∈ totFil X s (a + 1) := by
  intro K _ _ X s hs δ Co a ha
  obtain ⟨hle, hker⟩ := GlobalTheory.HSCore.filV_symV_ker K X s hs δ Co a ha
  refine ⟨Submodule.map_mono hle, fun x => ?_⟩
  let e := Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a)
  let y : filV X s a := e.symm x
  have hxy : e y = x := e.apply_symm_apply x
  have hx1 : x.1 = incl X X.T y.1 := by rw [← hxy]; rfl
  have : totSym Co a x = symV Co a y := rfl
  rw [this, hker y, hx1]
  constructor
  · intro h
    exact ⟨y.1, h, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [← incl_injective X X.T hzy]

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreePencilLineDiscriminantLeStatement
section
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalDegree_pencilLineDiscriminant_le : ∀ (F : Type) [Field F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsMultiHomogeneous (fun _ => δ) f → ∀ ξ₀ ξ₁ : Fin N → F, (GlobalTheory.PencilDisc.disc δ (fun i j => (MvPolynomial.X (i, j) : MvPolynomial (Fin D × Fin N) F)) (fun j => MvPolynomial.C (ξ₀ j)) (fun j => MvPolynomial.C (ξ₁ j)) f).totalDegree ≤ 2 * D * δ ^ 2 := by
  first | exact @GlobalTheory.PencilDiscDeg.totalDegree_disc_le | exact GlobalTheory.PencilDiscDeg.totalDegree_disc_le | (intros; apply GlobalTheory.PencilDiscDeg.totalDegree_disc_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacLn

def trPair (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
    (fun c x y => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun c x y => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul])

theorem trPair_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) :
    trPair F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

def coord {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} (d : Darboux B κ) (w : W) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) :=
  (fun i => evI F ((d.e w).1 i), fun i => evI F ((d.e w).2 i))

end GlobalTheory.VacLn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPureTensorsProductMeasureFiniteAdelicStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_pureTensors_productMeasure_finiteAdelic : ∀ (D : D7) (V V' : HSp D) (j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) → ∀ Φ : GfC V ≃ₜ* GfC V', (∀ v g, Φ (locFin V v g) = locFin V' v (j v g)) → (∀ ff g, finFn V' (transfer j ff) (Φ g) = finFn V ff g) ∧ ∀ μf ν, IsFinMeas V μf ν → IsFinMeas V' (fun v => (μf v).map (j v)) (ν.map Φ) := by
  first | exact @GlobalTheory.TrMultTransport.transport | exact GlobalTheory.TrMultTransport.transport | (intros; apply GlobalTheory.TrMultTransport.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFinitenessSeparableNormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_finiteness_separable_norm : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → ∀ δ : GL (Fin n) (KQ p K r), (nrmRes p K n r δ).val.charpoly.Separable → GlobalTheory.TwFin.TwFin (sigRes p K n r) (Kres p K n r) δ (nrmRes p K n r δ) := by
  first | (exact @GlobalTheory.TwFinGL.main) | (exact GlobalTheory.TwFinGL.main) | (intros; apply GlobalTheory.TwFinGL.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalTermEqFinprodLocalTermsStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalTerm_eq_finprod_localTerms : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v) → ∀ x, GlobalTheory.EulerAbs.twTerm θ (⨅ v, (K v).comap (pf v)) δ f x = ∏ᶠ v, GlobalTheory.EulerAbs.twTerm (θv v) (K v) (pf v δ) (fv v) (pf v x) := by
  first | exact @GlobalTheory.EulerAbs.twTerm_eq_finprod | exact GlobalTheory.EulerAbs.twTerm_eq_finprod | (intros; apply GlobalTheory.EulerAbs.twTerm_eq_finprod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPiMulWeightLengthLeMaxWeightDegreeSqStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_pi_mul_weightLength_le_maxWeightDegree_sq : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), 2 * Real.pi * (Tp.nWn : ℝ) ≤ (GlobalTheory.IndexAssembly.topDeg Tp hK : ℝ) ^ 2 := by
  first | exact @GlobalTheory.TopDegLower.two_pi_nW_le_topDeg_sq | exact GlobalTheory.TopDegLower.two_pi_nW_le_topDeg_sq | (intros; apply GlobalTheory.TopDegLower.two_pi_nW_le_topDeg_sq <;> assumption)
end

