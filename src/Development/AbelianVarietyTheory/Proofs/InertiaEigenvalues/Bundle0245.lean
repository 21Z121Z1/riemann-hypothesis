import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfLocallyConstant
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.UnramifiedClasses

theorem eq_zero_of_locallyConstant {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type} [AddCommGroup A] (I : Subgroup G) (φ : G)
    (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤) (c : G → A)
    (hlc : IsLocallyConstant c) (hc : ∀ g h, c (g * h) = c g + c h) (hφ : c φ = 0)
    (hI : ∀ g ∈ I, c g = 0) (g : G) : c g = 0 := by
  have h1 : c 1 = 0 := by
    have := hc 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  let H : Subgroup G :=
    { carrier := {g | c g = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hc, ha, hb, add_zero]
      one_mem' := h1
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have := hc a a⁻¹
        rw [mul_inv_cancel, h1, ha, zero_add] at this
        exact this.symm }
  have hle : Subgroup.zpowers φ ⊔ I ≤ H :=
    sup_le ((Subgroup.zpowers_le (G := G)).mpr hφ) (fun g hg => hI g hg)
  have hcl : (Subgroup.zpowers φ ⊔ I).topologicalClosure ≤ H :=
    Subgroup.topologicalClosure_minimal _ hle (hlc.isClosed_fiber 0)
  rw [hgen] at hcl
  exact hcl (Subgroup.mem_top g)

theorem isLocallyConstant_mkQ {X : Type} [TopologicalSpace X] {O V : Type} [CommRing O]
    [AddCommGroup V] [Module O V] [TopologicalSpace V] [ContinuousAdd V] (T : Submodule O V)
    (hT : IsOpen (T : Set V)) (f : X → V) (hf : Continuous f) :
    IsLocallyConstant (fun x => T.mkQ (f x)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => f y + (-f x)) ⁻¹' (T : Set V),
    hT.preimage (hf.add continuous_const), by simp, fun y hy => ?_⟩
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, sub_eq_add_neg]
  exact hy

theorem exists_not_mem_range {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field LL] [Algebra O LL] [IsFractionRing O LL] :
    ∃ y : LL, y ∉ Set.range (algebraMap O LL) := by
  by_contra h
  push Not at h
  apply IsDiscreteValuationRing.not_isField O
  exact (RingEquiv.ofBijective (algebraMap O LL)
    ⟨IsFractionRing.injective O LL, h⟩).toMulEquiv.isField (Field.toIsField LL)

theorem HfD_eq_unramified : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) [IsTopologicalGroup G] [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL] [IsTopologicalRing LL], GoodO (Qp := Qp) LL O → ∀ (T : LocLat G Qp LL O), Module.finrank LL T.V = 1 → (∀ g x, T.ρ g x = x) → Module.finrank LL (FiniteCohomology PD T.ρ) = 1 → ∀ (I : Subgroup G) (φ : G), (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤ → ∀ δ : G → LL, δ ∈ finiteCocycles PD (1 : Representation LL G LL) → (∀ g ∈ I, δ g = 0) → δ ≠ 0 → HfD PD T.L ≠ ⊥ ∧ ∀ c : G → T.V ⧸ T.L.T, c ∈ HfD PD T.L ↔ (c ∈ divisibleCocycles T.L ∧ ∃ x, ∀ g ∈ I, c g = actD T.L g x - x) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD _ _ LL _ _ _ O _ _ _ hO T hV hρ
    hH I φ hgen δ hδ hδI hδ0
  have hopen := GlobalTheory.Cyc.locLat_isOpen hO T
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := hO
  obtain ⟨⟨e, he⟩, -⟩ := GlobalTheory.LineLattice.lattice_rank_one T.L hV
  obtain ⟨y₀, hy₀⟩ := exists_not_mem_range (O := O) (LL := LL)
  obtain ⟨⟨hδc, hδh⟩, x₀, hx₀⟩ := hδ
  have hδadd : ∀ g h, δ (g * h) = δ g + δ h := fun g h => by simpa using hδh g h
  have hact : ∀ g (x : T.V ⧸ T.L.T), actD T.L g x = x := by
    intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg (Submodule.Quotient.mk (p := T.L.T)) (hρ g x)
  have hBD : BD T.L = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [hact]
  have hB1 : B1 T.ρ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [cob, hρ]
  have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  have hc₀c : Continuous fun g => e (δ g) := by
    have : (fun g => e (δ g)) = fun g => δ g • e 1 := by
      funext g
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [this]
    exact hδc.smul continuous_const
  have hc₀ : (fun g => e (δ g)) ∈ finiteCocycles PD T.ρ := by
    let m := AlgebraTensorModule.map (e : LL →ₗ[LL] T.V) (LinearMap.id : B →ₗ[Qp] B)
    have hm : ∀ g y, m (actVB PD (1 : Representation LL G LL) g y) = actVB PD T.ρ g (m y) := by
      intro g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [m, actVB, hρ]
      | add a b ha hb => simp only [map_add, ha, hb]
    refine ⟨⟨hc₀c, fun g h => by simp only [hδadd, map_add, hρ]⟩, m x₀, fun g => ?_⟩
    have := congrArg m (hx₀ g)
    simp only [m, AlgebraTensorModule.map_tmul, LinearMap.id_apply, map_sub] at this
    rw [← hm]
    exact this
  obtain ⟨g₀, hg₀⟩ : ∃ g, δ g ≠ 0 := Function.ne_iff.mp hδ0
  have hdim : Module.finrank LL ↥(finiteCocycles PD T.ρ) = 1 := by
    rw [← hH]
    refine (Submodule.quotEquivOfEqBot _ ?_).finrank_eq.symm
    rw [hB1, Submodule.comap_bot, Submodule.ker_subtype]
  have hspan : ∀ z ∈ finiteCocycles PD T.ρ, ∃ a : LL, ∀ g, z g = e (a * δ g) := by
    intro z hz
    have hne : (⟨_, hc₀⟩ : ↥(finiteCocycles PD T.ρ)) ≠ 0 := by
      intro h
      have := congrFun (congrArg Subtype.val h) g₀
      exact hg₀ (by simpa using this)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨z, hz⟩
    refine ⟨a, fun g => ?_⟩
    have := congrFun (congrArg Subtype.val ha) g
    rw [← smul_eq_mul, map_smul]
    exact this.symm

  let r : LL → G → T.V ⧸ T.L.T := fun a g => T.L.T.mkQ (e (a * δ g))
  have hHf : ∀ c, c ∈ HfD PD T.L ↔ ∃ a, c = r a := by
    intro c
    unfold HfD
    rw [hBD, sup_bot_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨a, ha⟩ := hspan z hz
      exact ⟨a, funext fun g => by simp [r, ha]⟩
    · rintro ⟨a, rfl⟩
      refine ⟨a • fun g => e (δ g), (finiteCocycles PD T.ρ).smul_mem a hc₀, ?_⟩
      funext g
      simp [r, ← map_smul]
  have hrlc : ∀ a, IsLocallyConstant (r a) := fun a => by
    refine isLocallyConstant_mkQ T.L.T hopen (fun g => e (a * δ g)) ?_
    have : (fun g => e (a * δ g)) = fun g => a • e (δ g) := by
      funext g
      rw [← map_smul, smul_eq_mul]
    rw [this]
    exact hc₀c.const_smul a
  have hradd : ∀ a g h, r a (g * h) = r a g + r a h := fun a g h => by
    simp only [r, hδadd, mul_add, map_add]
  have hrI : ∀ a, ∀ g ∈ I, r a g = 0 := fun a g hg => by
    simp only [r, hδI g hg, mul_zero, map_zero]
  have hr₀ : r (y₀ / δ g₀) g₀ ≠ 0 := by
    intro h
    simp only [r, div_mul_cancel₀ _ hg₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    exact hy₀ ((he _).mp h)
  have hφ : δ φ ≠ 0 := by
    intro h
    exact hr₀ (eq_zero_of_locallyConstant I φ hgen _ (hrlc _) (hradd _)
      (by simp only [r, h, mul_zero, map_zero]) (hrI _) g₀)
  refine ⟨fun h => ?_, fun c => ?_⟩
  · have : r (y₀ / δ g₀) ∈ HfD PD T.L := (hHf _).mpr ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hr₀ (congrFun this g₀)
  · rw [hHf]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨hrlc a, fun g h => by rw [hact, hradd]⟩, 0, fun g hg => by
        rw [hrI a g hg, hact, sub_zero]⟩
    · rintro ⟨⟨hlc, hcoc⟩, x, hx⟩
      obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (c φ)
      refine ⟨e.symm v / δ φ, funext fun g => sub_eq_zero.mp ?_⟩
      refine eq_zero_of_locallyConstant I φ hgen (fun g => c g - r (e.symm v / δ φ) g)
        (hlc.sub (hrlc _)) (fun g h => ?_) ?_ (fun g hg => ?_) g
      · simp only [hcoc, hact, hradd]
        abel
      · simp only [r, div_mul_cancel₀ _ hφ, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, hv,
          sub_self]
      · simp only [hx g hg, hact, hrI _ g hg, sub_self]

end GlobalTheory.UnramifiedClasses
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompat
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem ioE_fixed_of_resΓ_eq_one (hO : Function.Injective (algebraMap O LL)) (g : G)
    (hg : W.resΓ g = 1) (e : W.EE) : gR g (E.ioE e) = E.ioE e := by
  rw [← GlobalTheory.TorsionBoundCompare.ioE_γ E hO g e, hg, map_one]
  rfl

theorem ioE_letπ : E.ioE (algebraMap (LetA O n) W.EE letπ) = inclR πA := by
  rw [E.ioE_ext, E.io_π]

theorem ioE_bounded_pole {p : ℕ} (hp : PD.p = p) (e : W.EE) :
    ∃ c : ℕ, Near (inclR : RA →+* RW) p (inclR πA) 0 (inclR πA ^ c * E.ioE e) := by
  obtain ⟨a, m, h⟩ := W.EE_dense e 1
  rw [pow_one, Ideal.mem_span_singleton, hp] at h
  obtain ⟨r, hr⟩ := h
  have h1 := congrArg E.ioE hr
  rw [map_sub, map_mul, map_mul, map_natCast, map_pow, map_pow, ioE_letπ, E.ioE_ext] at h1
  refine ⟨m, E.io a, E.ioE r, ?_⟩
  rw [pow_zero, one_mul, ← h1]
  change _ = inclR (E.io a) + _
  ring

end Generic

theorem ioE_compat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ e, E.tie.ioE (W.φE e) = φRW LL (E.tie.ioE e)) ∧ (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ e, AI.gRW LL (g : GQ l) (E.tie.ioE e) = E.tie.ioE e) ∧ E.tie.ioE (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ) = piR AI LL s ∧ (∀ e, ∃ c : ℕ, NearPi AI LL s 0 (piR AI LL s ^ c * E.tie.ioE e)) := by
  intro l _ P AI K s LL h W E
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  exact ⟨fun e => GlobalTheory.TorsionBoundCompare.ioE_φ E.tie hO e,
    fun g hg e => ioE_fixed_of_resΓ_eq_one E.tie hO g hg e, ioE_letπ E.tie,
    fun e => ioE_bounded_pole E.tie (P.PD_p K) e⟩

end GlobalTheory.Decompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExactOfTieLattice
section
noncomputable section

namespace GlobalTheory.EtaleExactLat

section Generic

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.EtaleExact TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem exact_of_tie_lattice (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (T Yt Z : LocLat G Qp LL O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L)
    (h1 : Function.Injective ι.f) (h3 : ∀ z ∈ Z.L.T, ∃ x ∈ Yt.L.T, π.f x = z)
    (h4 : ∀ x ∈ Yt.L.T, π.f x = 0 ↔ ∃ y ∈ T.L.T, ι.f y = x) :
    Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := by
  have hι : Function.Injective (latMap ι) := fun x y hxy =>
    Subtype.ext (h1 (congrArg Subtype.val hxy))
  have hπ : Function.Surjective (latMap π) := fun y => by
    obtain ⟨x, hx, hxy⟩ := h3 y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hex : Function.Exact (latMap ι) (latMap π) := fun x => by
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := (h4 x x.2).1 (congrArg Subtype.val hx)
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext ((h4 _ (latMap ι y).2).2 ⟨y, y.2, rfl⟩)
  haveI := Z.L.free
  have hπR : Function.Surjective ((latMap π).baseChange RW) :=
    LinearMap.lTensor_surjective RW hπ
  have hexR : Function.Exact ((latMap ι).baseChange RW) ((latMap π).baseChange RW) :=
    lTensor_exact RW hex hπ
  have hιR : Function.Injective ((latMap ι).baseChange RW) := by
    obtain ⟨s, hs⟩ := (latMap π).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hπ)
    obtain ⟨r, hr⟩ : ∃ r, r ∘ₗ latMap ι = LinearMap.id :=
      ((hex.split_tfae hι hπ).out 0 1).1 (show ∃ s, latMap π ∘ₗ s = LinearMap.id from ⟨s, hs⟩)
    refine Function.LeftInverse.injective (g := r.baseChange RW) fun x => ?_
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
    rfl
  have hsurj : Function.Surjective (W.map π) := by
    rw [← LinearMap.range_eq_top]
    refine eq_top_DD E hm Z _ ?_
    rw [span_range_map, LinearMap.range_eq_top.2 hπR]
  have hcomp : ∀ x, W.map π (W.map ι x) = 0 := fun x => by
    apply E.jD_inj
    rw [jD_map', jD_map', map_zero]
    exact hexR.apply_apply_eq_zero _
  refine ⟨fun x y hxy => E.jD_inj T (hιR ?_), fun y => ⟨fun hy => ?_, ?_⟩, hsurj⟩
  · rw [← jD_map', ← jD_map', hxy]
  · haveI := (W.DD_free Z).1
    obtain ⟨s, hs⟩ := (W.map π).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
    have hs' : ∀ z, W.map π (s z) = z := fun z => LinearMap.congr_fun hs z
    have htop : LinearMap.range (W.map ι) ⊔ LinearMap.range s = ⊤ := by
      refine eq_top_DD E hm Yt _ ?_
      set U := Submodule.span RW (E.jD Yt '' ((LinearMap.range (W.map ι) ⊔ LinearMap.range s :
        Submodule W.EE (W.DD Yt)) : Set (W.DD Yt))) with hU
      have hk : LinearMap.ker ((latMap π).baseChange RW) ≤ U := by
        rw [LinearMap.exact_iff.1 hexR, ← span_range_map E]
        exact Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 le_sup_left))
      have hmap : U.map ((latMap π).baseChange RW) = ⊤ := by
        rw [eq_top_iff, ← E.jD_span Z, Submodule.span_le]
        rintro _ ⟨z, rfl⟩
        refine ⟨E.jD Yt (s z), Submodule.subset_span
          ⟨s z, Submodule.mem_sup_right ⟨z, rfl⟩, rfl⟩, ?_⟩
        rw [← jD_map', hs']
      have := Submodule.comap_map_eq ((latMap π).baseChange RW) U
      rw [hmap, Submodule.comap_top, sup_eq_left.2 hk] at this
      exact this.symm
    obtain ⟨_, ⟨t, rfl⟩, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top (x := y))
    rw [map_add, hcomp, hs', zero_add] at hy
    exact ⟨t, by rw [hy, map_zero, add_zero]⟩
  · rintro ⟨x, rfl⟩
    exact hcomp x

end Generic

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem DD_exact_lattice : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (E : LocFon l P AI H) (K LL : FinExt l) (s : ℕ) (h : Good K s LL) (T' T T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T'.L T.L) (g : LatHom T.L T''.L), Function.Injective f.f → (∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, g.f x = z) → (∀ x ∈ T.L.T, g.f x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) → Function.Injective ((H.W K s LL h).map f) ∧ Function.Surjective ((H.W K s LL h).map g) ∧ Function.Exact ((H.W K s LL h).map f) ((H.W K s LL h).map g) := by
  intro l _ P AI H E K LL s h T' T T'' f g hf hg hfg
  haveI := EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  have hp : (P.PD K).p = l := P.PD_p K
  have key := exact_of_tie_lattice (E.E K s LL h).tie
    (EtaleExact.map_ne_top_of_tie (E.E K s LL h).tie
      (by rw [hp]; exact EtaleExact.isUnit_or_dvd_pow P LL)
      (by rw [hp]; exact EtaleExact.sep_RW LL)) T' T T'' f g hf hg hfg
  exact ⟨key.1, key.2.2, key.2.1⟩

end GlobalTheory.EtaleExactLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisLogOneAdd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU

variable {l : ℕ} [Fact l.Prime]

theorem acris_lim_pt (s : ℕ → Per.Acris0 l)
    (hs : ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris0 l, s n - s (l ^ r) = ((l : ℕ) : Per.Acris0 l) ^ r * z) :
    ∃ y : Per.Acris l, ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris l,
      y - algebraMap (Per.Acris0 l) (Per.Acris l) (s n) = ((l : ℕ) : Per.Acris l) ^ r * z := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨y, hy⟩ := Model.pc_lim (l := l) (Per.Acris0 l) s hs
  refine ⟨e.symm y, fun r n hn => ?_⟩
  obtain ⟨z, hz⟩ := hy r n hn
  refine ⟨e.symm z, e.injective ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, e.apply_symm_apply, e.apply_symm_apply, he]
  exact hz

theorem frobenius_surjective_modP : Function.Surjective (frobenius (ModP (Per.OC l) l) l) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl
  have hb1 : b ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC]
    have := (GlobalTheory.RingBasics.mem_OC _).1 a.2
    rw [← hb, norm_pow] at this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne').1 this
  refine ⟨Ideal.Quotient.mk _ ⟨b, hb1⟩, ?_⟩
  rw [frobenius_def, ← map_pow]
  exact congrArg _ (Subtype.ext hb)

theorem θ_surjective : Function.Surjective (Per.θ l) :=
  surjective_fontaineTheta frobenius_surjective_modP

theorem exists_divPow {w : Per.Ainf l} (hw : InJ w) (k : ℕ) :
    ∃ g : Per.Acris0 l, ((k.factorial : ℕ) : Per.AinfP l) * (g : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) w ^ k := by
  obtain ⟨c, hc⟩ := hw
  obtain ⟨a, ha⟩ := θ_surjective (l := l) c
  have hz : Per.θ l (w - (l : Per.Ainf l) * a) = 0 := by
    rw [map_sub, map_mul, map_natCast, ha, hc, sub_self]
  have hd : ∀ j : ℕ, ∃ d : Per.AinfP l, d ∈ Per.Acris0 l ∧ ((j.factorial : ℕ) : Per.AinfP l) * d =
      algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j := by
    intro j
    obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ j.factorial_ne_zero).exists_right_inv
    have e : ((j.factorial : ℕ) : Per.AinfP l) *
        (u * algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j) =
        algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j := by
      rw [← mul_assoc, hu, one_mul]
    exact ⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l _ j _ hz e, e⟩
  choose d hdm hdd using hd
  choose q hq using fun m : ℕ => GlobalTheory.RingBasics.exists_pow_div_factorial l m
  let ζ : ℤ_[l] →+* Per.AinfP l := (algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)
  have hq' : ∀ m : ℕ, ((m.factorial : ℕ) : Per.AinfP l) * ζ (q m) = ((l : ℕ) : Per.AinfP l) ^ m := by
    intro m
    have h := congrArg ζ (hq m)
    rwa [map_mul, map_natCast, map_pow, map_natCast] at h
  have hg : (∑ m ∈ Finset.range (k + 1), ζ (q m) * algebraMap (Per.Ainf l) (Per.AinfP l) a ^ m *
      d (k - m)) ∈ Per.Acris0 l := by
    refine Subalgebra.sum_mem _ fun m _ => mul_mem (mul_mem ?_ (pow_mem (Subalgebra.algebraMap_mem _ _) _))
      (hdm _)
    exact Subalgebra.algebraMap_mem _ (Per.zA l (q m))
  refine ⟨⟨_, hg⟩, ?_⟩
  have hw' : algebraMap (Per.Ainf l) (Per.AinfP l) w = ((l : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) a +
      algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) := by
    rw [map_sub, map_mul, map_natCast]
    ring
  show _ * ∑ m ∈ Finset.range (k + 1), _ = _
  rw [hw', add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have hf : ((k.factorial : ℕ) : Per.AinfP l) = ((k.choose m : ℕ) : Per.AinfP l) *
      ((m.factorial : ℕ) : Per.AinfP l) * (((k - m).factorial : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial hmk]
  rw [hf, mul_pow, ← hq' m, ← hdd (k - m)]
  ring

theorem exists_isLogJ : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l), InJ w → ∃ y : Per.Acris l, IsLogJ w y := by
  intro l _ w hw
  have hl : l.Prime := Fact.out
  choose g hg using exists_divPow hw
  let s : ℕ → Per.Acris0 l := fun n =>
    ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * g (k + 1)
  obtain ⟨y, hy⟩ := acris_lim_pt s (by
    intro r n hn
    have : ((l : ℕ) : Per.Acris0 l) ^ r ∣ s n - s (l ^ r) := by
      simp only [s]
      rw [← Finset.sum_Ico_eq_sub _ hn]
      refine Finset.dvd_sum fun k hk => ?_
      have h1 : l ^ r ∣ k.factorial := Nat.dvd_factorial (pow_pos hl.pos r) (Finset.mem_Ico.1 hk).1
      have h2 : ((l : ℕ) : Per.Acris0 l) ^ r ∣ ((k.factorial : ℕ) : Per.Acris0 l) := by
        exact_mod_cast Nat.cast_dvd_cast (α := Per.Acris0 l) h1
      exact (h2.mul_left _).mul_right _
    exact this)
  refine ⟨y, fun r => ⟨l ^ r, fun n hn => ⟨s n, ?_, hy r n hn⟩⟩⟩
  simp only [s]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : n.factorial = n.factorial / (k + 1) * (k + 1) :=
    (Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm
  have h2 : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (k + 1) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → Per.AinfP l) h1
  rw [← hg (k + 1), Nat.factorial_succ]
  generalize ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) = q at h2 ⊢
  rw [h2]
  push_cast
  ring

end GlobalTheory.LogU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousNormCharLFunctionNeZeroOneStatement
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_normCharLFunction_ne_zero_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → ∀ (χ : (ZMod m)ˣ →* ℂˣ) (cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ), (∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ)) → (∃ P, ¬ m ∣ Ideal.absNorm P.asIdeal ∧ χ (cl P) ≠ 1) → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s → Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - ((χ (cl P) : ℂˣ) : ℂ) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)))) = L s := by
  first | exact @GlobalTheory.NormCharL.exists_continuous_ne_zero_one | exact GlobalTheory.NormCharL.exists_continuous_ne_zero_one | (intros; apply GlobalTheory.NormCharL.exists_continuous_ne_zero_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwistStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRhamFil_graded_symbol_to_tate_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ThetaL P AI → ∀ (K : FinExt l), ∃ sy : ℤ → P.R.BdR → PadicComplex l, ∀ a : ℤ, (∀ x ∈ (P.PD K).Fil a, ∀ y ∈ (P.PD K).Fil a, sy a (x + y) = sy a x + sy a y) ∧ (∀ (c : Om l), ∀ x ∈ (P.PD K).Fil a, sy a (algebraMap (Om l) P.R.BdR c * x) = (c : PadicComplex l) * sy a x) ∧ (∀ x ∈ (P.PD K).Fil a, sy a x = 0 ↔ x ∈ (P.PD K).Fil (a + 1)) ∧ ∀ (g : GQ l), ∀ x ∈ (P.PD K).Fil a, sy a (P.actQdR g x) = chiC P.χQ a g * AI.actC g (sy a x) := by
  first | exact @GlobalTheory.DeRhamSymbol.exists_symbol | exact GlobalTheory.DeRhamSymbol.exists_symbol | (intros; apply GlobalTheory.DeRhamSymbol.exists_symbol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamTensorCoordinatesOfBasisStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), ∃ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (a : ℤ) (z : V ⊗[Qp] BdR), z ∈ FilV PD (LL := LL) (V := V) a ↔ ∀ i, Φ z i ∈ PD.Fil a) ∧ ∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i)) := by
  first | exact @GlobalTheory.exists_coord_tensor_dR | exact GlobalTheory.exists_coord_tensor_dR | (intros; apply GlobalTheory.exists_coord_tensor_dR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltRootOfUnityApproxRatioStatement
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tilt_root_of_unity_approx_ratio : ∀ (l : ℕ) [Fact l.Prime] (y y' : Formalism.Per.Fl l), y' ≠ 0 → ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ → ∃ (ζ : Formalism.Per.Fl l) (o : ℕ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ ‖(((y - ζ * y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ < ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  first | exact @GlobalTheory.TiltRootApprox.exists_root_approx | exact GlobalTheory.TiltRootApprox.exists_root_approx | (intros; apply GlobalTheory.TiltRootApprox.exists_root_approx <;> assumption)
end

