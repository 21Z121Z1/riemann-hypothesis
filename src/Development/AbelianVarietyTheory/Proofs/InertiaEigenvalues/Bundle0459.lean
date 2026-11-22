import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCoeffOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0184
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0177
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0231
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGammaLayerPadicCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTensorAinfGaloisStableKummerFixed
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.StableFix

theorem SemiBC.span_eq {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) :
    Submodule.span B (Set.range u) = ⊤ := by
  have h1 : (Submodule.span B (Set.range u)).mkQ = 0 := h.hom_ext fun x => by
    rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨x, rfl⟩
  exact Submodule.eq_top_iff'.2 fun y => by
    have := LinearMap.congr_fun h1 y
    rwa [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem kappa_act {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (s : GQ l) (g : G) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, TWact (galOW O s) T g (kappa T y) =
      kappa T (TensorProduct.map (galW l s).toLinearMap (actZ T g) y) := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem kappa_smul' {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (w : WCb l) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (w • y) = ((1 : O) ⊗ₜ[ℤ_[l]] w) • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w' x =>
    rw [smul_tmul', kappa_tmul, kappa_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable (P : PhiMod O K l e a ι)

theorem inclO_smul_mem_MA (r : OA l O) {v : ι → OW l O} (hv : v ∈ MA P) : inclO l O r • v ∈ MA P := by
  obtain ⟨c, rfl⟩ := hv
  exact ⟨r • c, funext fun i => (map_mul (inclO l O) r (c i))⟩

theorem inclO_smul_mem_LA (r : OA l O) {v : ι → OW l O} (hv : v ∈ LA t ϖ P) : inclO l O r • v ∈ LA t ϖ P := by
  obtain ⟨c, rfl⟩ := hv
  refine ⟨r • c, ?_⟩
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul (inclO l O) r (c i))

abbrev eb (i : ι) : ι → OW l O := fun j => if i = j then 1 else 0

theorem phiW_eb (i : ι) : phiW t ϖ P (eb i) = frobMat t ϖ P *ᵥ eb i := by
  rw [phiW_apply]
  congr 1
  funext j
  show frobOW l O (if i = j then 1 else 0) = if i = j then 1 else 0
  split_ifs <;> simp

theorem phiW_inclV (c : ι → OA l O) : phiW t ϖ P (inclV l O ι c) = inclL t ϖ P (fun i => frobOA l O (c i)) := by
  rw [phiW_apply, inclL_apply]
  congr 1
  funext j
  exact frobOW_inclO (c j)

def mb (i : ι) : Vec K a ι := fun _ j => if i = j then 1 else 0

theorem mb_mem (i : ι) : (mb i : Vec K a ι) ∈ P.M :=
  mem_tot.2 fun τ j => by
    change (if i = j then (1 : K⟦X⟧) else 0) ∈ A O K
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem toW_mb (i : ι) : toW t ϖ P ⟨mb i, mem_ME_of_mem_M (mb_mem P i)⟩ = eb i := by
  funext j
  rw [toW_apply]
  show _ = (if i = j then (1 : OW l O) else 0)
  split_ifs with h
  · convert map_one (ϖ.iW t K) using 2
    funext τ
    apply Subtype.ext
    simp [mb, h]
  · convert map_zero (ϖ.iW t K) using 2
    funext τ
    apply Subtype.ext
    simp [mb, h]

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem add_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T))
      (z z' : E.M (ainfObj (ϖ.field a))) (v v' : ι → OW l O), I.j v = kappa T (j z) → I.j v' = kappa T (j z') →
      I.j (v + v') = kappa T (j (z + z')) := by
  letI := zlLat T
  intro j z z' v v' hv hw
  rw [I.j.map_add, hv, hw, j.map_add, (kappa T).map_add]

theorem smul_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T))
      (c : (ainfObj (ϖ.field a)).A) (z : E.M (ainfObj (ϖ.field a))) (v : ι → OW l O), I.j v = kappa T (j z) →
      I.j (inclO l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfId (ϖ.field a) c) • v) = kappa T (j (c • z)) := by
  letI := zlLat T
  intro j c z v hv
  have e1 : j (c • z) = inclW l (ainfId (ϖ.field a) c) • j z := j.map_smulₛₗ c z
  rw [e1, kappa_smul', LinearEquiv.map_smul, hv, inclO_tmul]

theorem span_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)),
      (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (j (E.tr (ϖ.toAinf a) x))) ↔
        ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) →
      ∀ z : E.M (ainfObj (ϖ.field a)), ∃ v ∈ MA P, I.j v = kappa T (j z) := by
  letI := zlLat T
  intro j hE z
  have hz : z ∈ Submodule.span (ainfObj (ϖ.field a)).A (Set.range (E.tr (ϖ.toAinf a))) := by
    rw [SemiBC.span_eq (E.tr_bc (ϖ.toAinf a))]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, rfl⟩ := hz
    obtain ⟨m', hm', h'⟩ := (hE (kappa T (j (E.tr (ϖ.toAinf a) y)))).1 ⟨y, rfl⟩
    exact ⟨_, toW_mem_MA t ϖ P hm', h'.symm⟩
  | zero => exact ⟨0, zero_mem _, by rw [I.j.map_zero, j.map_zero, (kappa T).map_zero]⟩
  | add z z' _ _ h h' =>
    obtain ⟨v, hv, hv'⟩ := h
    obtain ⟨v', hw, hw'⟩ := h'
    exact ⟨v + v', add_mem hv hw, add_step I E j z z' v v' hv' hw'⟩
  | smul c z _ h =>
    obtain ⟨v, hv, hv'⟩ := h
    exact ⟨_, inclO_smul_mem_MA P _ hv, smul_step I E j c z v hv'⟩

theorem core {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (hI : IsBK I)
    (g : ↥(GK (ϖ.field a))) (m : Vec K a ι) (hm : m ∈ P.M) :
    I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) ∈ MA P ∧
      ((g : GQ l) ∈ ϖ.GfieldInf a →
        I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) = toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := by
  letI := zlLat T
  obtain ⟨E, j, H, hE⟩ := hI
  obtain ⟨x, hx⟩ := (hE (I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩))).2 ⟨m, hm, rfl⟩
  have hact : I.j (I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) =
      kappa T (j (E.tr (ainfHom (ϖ.field a) g) (E.tr (ϖ.toAinf a) x))) := by
    rw [Ident.j_act, hx, kappa_act]
    exact congrArg (kappa T) (H.j_act g _).symm
  refine ⟨?_, fun hg => I.j.injective ?_⟩
  · obtain ⟨v, hv, hv'⟩ := span_step I E j hE (E.tr (ainfHom (ϖ.field a) g) (E.tr (ϖ.toAinf a) x))
    rw [← hact, I.j.injective.eq_iff] at hv'
    exact hv' ▸ hv
  · have h1 : (ainfHom (ϖ.field a) g).comp (ϖ.toAinf a) = ϖ.toAinf a :=
      Hom.ext' (RingHom.ext fun y => PiSys.gal_ev l a ϖ hg y)
    rw [hact, ← E.tr_comp, h1, ← hx]

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : PhiMod O K l e a ι} {T : Lat a O K ϖ}

theorem act_eb_mem (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) (i : ι) :
    I.act (g : GQ l) g (eb i) ∈ MA P := by
  rw [← toW_mb P i]
  exact (core I hI g _ (mb_mem P i)).1

theorem act_MA (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) :
    ∀ v ∈ MA P, I.act (g : GQ l) g v ∈ MA P := by
  rintro _ ⟨c, rfl⟩
  rw [pi_eq_sum_univ (inclV l O ι c), map_sum]
  refine sum_mem fun i _ => ?_
  rw [Ident.act_smul]
  change galOW O (g : GQ l) (inclO l O (c i)) • _ ∈ _
  rw [galOW_inclO]
  exact inclO_smul_mem_MA P _ (act_eb_mem I hI g i)

theorem act_LA (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) :
    ∀ v ∈ LA t ϖ P, I.act (g : GQ l) g v ∈ LA t ϖ P := by
  rintro _ ⟨c, rfl⟩
  have h1 : inclL t ϖ P c = ∑ i, inclO l O (c i) • phiW t ϖ P (eb i) := by
    rw [inclL_apply]
    conv_lhs => rw [pi_eq_sum_univ (fun i => inclO l O (c i)), Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, phiW_eb]
  rw [h1, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Ident.act_smul, galOW_inclO, Ident.act_phiW]
  refine inclO_smul_mem_LA P _ ?_
  obtain ⟨d, hd⟩ := act_eb_mem I hI g i
  rw [← hd, phiW_inclV]
  exact ⟨_, rfl⟩

theorem act_fix (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) (hg : (g : GQ l) ∈ ϖ.GfieldInf a)
    (v : ME P) : I.act (g : GQ l) g (toW t ϖ P v) = toW t ϖ P v := by
  conv_lhs => rw [pi_eq_sum_univ (toW t ϖ P v), map_sum]
  conv_rhs => rw [pi_eq_sum_univ (toW t ϖ P v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ident.act_smul, toW_apply, ϖ.galOW_iW t K hg]
  congr 1
  have h := (core I hI g _ (mb_mem P i)).2 hg
  rw [toW_mb P i] at h
  exact h

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) ∧ ∀ g : Gl l, sQ l g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I hBK
  refine ⟨fun g => ⟨act_LA _ hBK g, act_MA _ hBK g⟩, fun g hg v => ?_⟩
  exact act_fix (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) hBK
    ⟨sQ l g, PiSys.fixing_fieldInf_le a ϖ hg⟩ hg v

end GlobalTheory.BKGal.StableFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiGamPowNeOne
section
noncomputable section

namespace GlobalTheory.HWL.Cmp

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s}

variable {R : WSer Γ} {b₀ : LetA O n →+* LL ⊗[Qp] B} {tS zS : BdR}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n}

open Classical in

def levOf {Dc : Disc R b₀ tS zS} {Mo : WN E zl} (bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B)
    (Fr : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Frame Dc Mo T) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) :
    ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] B) :=
  if h : IsCrys PD T.ρ then (Fr T h).lev bT i ζ else 0

set_option maxHeartbeats 1000000 in
theorem nonempty_wCmp [NeZero n] (Dc : Disc R b₀ tS zS) (Mo : WN E zl) {ιdR : Ai →+* BdR} {p1 : Ai}
    {βdR : ∀ T : LocLat G Qp LL O, TW (O ⊗[Zl] Ai) T →+ T.V ⊗[Qp] BdR}
    {bT : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B} (hP : IsPer Mo b₀ ιdR p1 βdR bT)
    (Fr : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Frame Dc Mo T)
    (hinv : ∀ a : LetA LL n, γL R Γ.gam a = a → ∃ c, a = cst c) : Nonempty (WCmp Mo ιdR p1 tS zS) := by
  have pos : ∀ (T : LocLat G Qp LL O) (h : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL), levOf bT Fr T i ζ = Frame.lev bT (Fr T h) i ζ :=
    fun T h i ζ => dif_pos h
  have neg : ∀ (T : LocLat G Qp LL O) (_ : ¬ IsCrys PD T.ρ) (i : ZMod n) (ζ : LL), levOf bT Fr T i ζ = 0 := fun T h i ζ => dif_neg h
  have hmem : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ), levOf bT Fr T i ζ x k ∈ DcrisL PD T.ρ (Γ.emb i) := by
    intro T i ζ x k
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_mem hP h _ i ζ x k
    · rw [neg T h]; exact Submodule.zero_mem _
  have hsupp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)), ∃ m : ℤ, ∀ k < m, levOf bT Fr T i ζ x k = 0 := by
    intro T i ζ x
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact ⟨_, Frame.lev_supp bT _ i ζ x⟩
    · rw [neg T h]; exact ⟨0, fun _ _ => rfl⟩
  have hneg : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(Mo.N T)) (k : ℤ), k < 0 → levOf bT Fr T i 1 x k = 0 := by
    intro T i x k hk
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_one_neg bT _ i x k hk
    · rw [neg T h]; rfl
  have hsmul : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (α : LetA O n) (x : ↥(Mo.N T)) (k : ℤ), levOf bT Fr T i ζ (α • x) k =
      ∑ᶠ j : ℕ, PowerSeries.coeff j (R.lev i ζ α) • levOf bT Fr T i ζ x (k - (j : ℤ)) := by
    intro T i ζ α x k
    by_cases h : IsCrys PD T.ρ
    · rw [pos T h]; exact Frame.lev_smul bT _ i ζ α x k
    · rw [neg T h]; simp
  have hsmul0 : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (α : LetA O n) (x : ↥(Mo.N T)), levOf bT Fr T i 1 (α • x) 0 =
      PowerSeries.constantCoeff (R.lev i 1 α) • levOf bT Fr T i 1 x 0 := by
    intro T i α x
    rw [hsmul, finsum_eq_single _ 0]
    · simp
    · intro j hj
      rw [hneg T i x _ (by omega), smul_zero]
  let cmp : ∀ T : LocLat G Qp LL O, ↥(Mo.N T) →+ T.V ⊗[Qp] B := fun T =>
    ∑ i : ZMod n, (Pi.evalAddMonoidHom (fun _ : ℤ => T.V ⊗[Qp] B) 0).comp (levOf bT Fr T i 1)
  have hcmp : ∀ (T : LocLat G Qp LL O) (x : ↥(Mo.N T)), cmp T x = ∑ i : ZMod n, levOf bT Fr T i 1 x 0 := by
    intro T x
    simp [cmp, AddMonoidHom.finset_sum_apply]
  have hcmpE : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (x : ↥(Mo.N T)), cmp T ((letE i : LetA O n) • x) = levOf bT Fr T i 1 x 0 := by
    intro T i x
    rw [hcmp, Finset.sum_eq_single i]
    · rw [hsmul0, Dc.lev_letE]; simp
    · intro j _ hj
      rw [hsmul0, Dc.lev_letE]; simp [hj]
    · simp
  have hmap : ∀ {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
      ∀ (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (hx : E.map f (x : E.DD T) ∈ Mo.N T') (k : ℤ),
      levOf bT Fr T' i ζ ⟨E.map f (x : E.DD T), hx⟩ k =
        AlgebraTensorModule.map f.f (LinearMap.id : B →ₗ[Qp] B) (levOf bT Fr T i ζ x k) := by
    intro T T' f h h' i ζ x hx k
    rw [pos T h, pos T' h']
    exact Frame.lev_map hP hinv f h h' _ _ i ζ x hx k
  let levN : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(Mo.N T) →+ (ℤ → T.V ⊗[Qp] BdR) := fun T i ζ =>
    ((ιV PD (LL := LL) (V := T.V)).toAddMonoidHom.compLeft ℤ).comp (levOf bT Fr T i ζ)
  have hN : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(Mo.N T)) (k : ℤ), levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (levOf bT Fr T i ζ x k) :=
    fun _ _ _ _ _ => rfl
  refine ⟨{
    cmp := cmp
    cmp_smul := fun T c x => ?_
    cmp_π := fun T x => ?_
    cmp_mem := fun T x => ?_
    cmp_letter := fun T i x => by rw [hcmpE]; exact hmem T i 1 x 0
    cmp_map := fun f h h' x hx => by simp only [hcmp, hmap f h h', map_sum]
    levN := levN
    levN_supp := fun T i ζ x => ?_
    levN_smul := fun T i ζ α x k => ?_
    levN_map := fun {T T'} f h h' i ζ x hx k => ?_
    levB := levOf bT Fr
    levB_mem := hmem
    levB_supp := hsupp
    levN_eq := hN
    cmp_eq := fun T _ => hcmpE T
    levB_φ := fun T h i ζ hζ x m hx k => by
      simp only [pos T h]; exact Frame.lev_φ hP h _ i ζ hζ x m hx k
    levB_Γ := fun T h g i ζ ζ' j a h1 h2 h3 x hx k => by
      simp only [pos T h]; exact Frame.lev_Γ bT _ g i ζ ζ' j a h1 h2 h3 x hx k
    βdR := βdR
    βdR_tmul := hP.tmul
    levN_dR := fun T h i ζ ι h1 h2 x k y hy a ha => ?_ }⟩
  · have : c • x = algebraMap O (LetA O n) c • x := Subtype.ext (algebraMap_smul (LetA O n) c (x : E.DD T)).symm
    rw [this, hcmp, hcmp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul0, AlgHom.commutes]
    simp [PowerSeries.algebraMap_apply]
  · rw [hcmp]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨e, he, -, h3⟩ := R.lev_π i 1 ⟨0, by simp⟩
    have h4 := congrArg PowerSeries.constantCoeff h3
    rw [map_add, map_mul, he] at h4
    have h5 : PowerSeries.constantCoeff (R.lev i 1 letπ) = 0 := by simpa using h4
    rw [hsmul0, h5, zero_smul]
  · rw [hcmp]
    exact Submodule.sum_mem _ fun i _ => (hmem T i 1 x 0).1
  · obtain ⟨m, hm⟩ := hsupp T i ζ x
    exact ⟨m, fun k hk => by rw [hN, hm k hk, map_zero]⟩
  · obtain ⟨m, hm⟩ := hsupp T i ζ x
    have hz : ∀ j : ℕ, j ∉ Finset.range ((k - m).toNat + 1) → levOf bT Fr T i ζ x (k - (j : ℤ)) = 0 := by
      intro j hj
      have : (k - m).toNat + 1 ≤ j := by simpa using hj
      exact hm _ (by omega)
    rw [hN, hsmul, finsum_eq_sum_of_support_subset (s := Finset.range ((k - m).toNat + 1)),
      finsum_eq_sum_of_support_subset (s := Finset.range ((k - m).toNat + 1)), map_sum]
    · simp only [map_smul, hN]
    · intro j hj
      by_contra hc
      exact hj (by simp only [hN, hz j hc, map_zero, smul_zero])
    · intro j hj
      by_contra hc
      exact hj (by simp only [hz j hc, smul_zero])
  · rw [hN, hN, hmap f h h']
    induction levOf bT Fr T i ζ x k using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b => simp [ιV]
  · rw [hP.dR T h x k y hy]
    refine GlobalTheory.T.filtration_estimate_expansion_tensorBdR_component PD T ι tS (ιdR p1 ^ k) (Dc.ι_tb ▸ Dc.tb_unit.map PD.ι) Dc.tS_mem (Fr T h).r (Fr T h).w _
      (fun j => ιV PD (LL := LL) (V := T.V) ((Fr T h).d bT j)) _ (fun j => Dc.ex i ζ ((Fr T h).a x j)) _
      (Frame.dR_basis hP h (Fr T h) ι x) (fun j m => Dc.taylor i ζ ι h1 h2 _ m) (fun k => ?_) a ha
    rw [hN, pos T h]
    exact Frame.dR_lev (Fr T h) i ζ ι h1 h2 x k

end Generic

theorem chi_gam_pow_ne_one {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (hG : Good K s LL) (Γ : GamS P K s LL) (k : ℕ) (hk : 0 < k) :
    algebraMap ↥(OL LL) ↥LL.1 (Γ.χΓ Γ.gam : ↥(OL LL)) ^ k ≠ 1 := by
  intro h
  obtain ⟨⟨lam, -, h1, h2, ⟨g, hg⟩, -⟩, -⟩ := GlobalTheory.HWL.Coord.exists_gamma_coordinates l P K s LL hG Γ
  have h3 : Γ.gam ^ k = 1 := by
    apply Γ.χΓ_inj
    rw [map_pow, map_one]
    apply Units.ext
    apply Subtype.ext
    simpa using h
  have h4 : lam (g ^ k) = 1 := by
    rw [h1, Subgroup.coe_pow, map_pow, (h2 g).mp hg, h3]
  rw [map_pow, hg, ← ofAdd_nsmul, ofAdd_eq_one] at h4
  simp at h4
  omega

set_option maxHeartbeats 1000000 in

theorem nonempty_cmpS : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R),
    IoW I → ∀ (E : WEt I) (Mo : NS E), Nonempty (CmpS Mo) := by
  intro l _ P AI hT K s LL hG Γ R I hI E Mo
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.HWLBeta.exists_beta l P AI hT LL
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_evaluation_convergent_series_Bcris l P AI hT K s LL hG Γ R I hI β hβ
  obtain ⟨Dc, hC, ht⟩ := GlobalTheory.T.exists_openDiscConvergentRing_with_expansions l P AI hT K s LL hG Γ R I hI β hβ J hJ (GlobalTheory.T.cyclotomicPowerSeriesData_lev_isExpansionAtZeta l P K s LL Γ R)
    (GlobalTheory.T.maxUnramified_acts_on_letterIdempotent_image l P AI hT K s LL hG Γ R I hI β hβ)
  obtain ⟨βdR, bT, hP⟩ := GlobalTheory.T.exists_wachModule_periodMap_to_bcris l P AI hT K s LL hG Γ R I hI β hβ E Mo
    (GlobalTheory.T.wachLattice_ainf_sandwich_invert_pi l P AI K s LL hG Γ R I hI E Mo)
  have hF : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ → Nonempty (Frame Dc Mo T) := by
    intro T h
    obtain ⟨nb⟩ := GlobalTheory.T.wach_lattice_free_of_crystalline l P AI K s LL hG Γ R I hI E Mo T h
    obtain ⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_wachLattice_matrices_gamma_phi Mo T _ nb
    obtain ⟨U, V, w, k1, -, k3, k4, Cm, k5⟩ := GlobalTheory.T.exists_invariant_basis_converging_open_disc l P K s LL hG Γ R _ m m' Gm Pm Pm' h1 h2 h3 h4
    refine ⟨{
      r := _, w := w, m := m, nb := nb, U := U, V := V, UV := k1
      U_mem := fun i j => hC _ fun k => by rw [ht]; exact (k3 i j k).1
      V_mem := fun i j => hC _ fun k => by rw [ht]; exact (k3 i j k).2
      Gm := Gm, Gm_def := h5
      GU := fun g => ?_
      Pm := Pm, Pm_def := h6, Cm := Cm
      PU := ?_ }⟩
    · rw [funext (γL_apply R g)]
      exact k4 g
    · have e1 : ⇑(φL ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) (P.PD K).p) = fun a k =>
          PowerSeries.subst ((1 + PowerSeries.X) ^ l - 1 : PowerSeries ↥LL.1) (a (k - 1)) := by
        funext a
        rw [φL_apply, P.PD_p]
      have e2 : toL ↥(OL LL) ↥LL.1 _ (R.Q ^ m) = toLL R.Q ^ m := (toL ↥(OL LL) ↥LL.1 _).map_pow R.Q m
      rw [e1]
      exact k5.trans (congrArg (fun q : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) => q • (U * Cm.map cst)) e2.symm)
  refine nonempty_wCmp Dc Mo hP (fun T h => (hF T h).some) fun a ha => ?_
  refine ⟨fun i => PowerSeries.constantCoeff (a i), funext fun i => ?_⟩
  refine GlobalTheory.T.powerSeries_eq_C_of_subst_fixed_not_root_of_unity _ (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.γ₀ Γ.gam PowerSeries.X)) ?_ ?_ (a i) ?_
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (R.γ₀_X _).1, map_zero]
  · intro k hk
    rw [PowerSeries.coeff_map, (R.γ₀_X _).2]
    exact chi_gam_pow_ne_one hG Γ k hk
  · rw [γL_apply] at ha
    exact congrFun ha i

end GlobalTheory.HWL.Cmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescEqXPowSmulNablaPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.desc_eq_X_pow_smul_nabla_pow' : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (v : Vec K a ι), C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v := by
  first | exact @GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow | exact GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow | (intros; apply GlobalTheory.DescFalling.desc_eq_X_pow_smul_nabla_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescNEqXPowMulIterateDerivativeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descN_eq_X_pow_mul_iterate_derivative' : ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧), descN K p f = X ^ p * (⇑(derivative K))^[p] f := by
  first | exact @GlobalTheory.BKReal.descN_eq_X_pow_mul_iterate_derivative | exact GlobalTheory.BKReal.descN_eq_X_pow_mul_iterate_derivative | (intros; apply GlobalTheory.BKReal.descN_eq_X_pow_mul_iterate_derivative <;> assumption)
end

