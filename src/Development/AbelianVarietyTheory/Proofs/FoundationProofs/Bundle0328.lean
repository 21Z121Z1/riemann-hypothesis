import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodFormsCoordinateMapMemOfLiftsMem
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open Formalism.IndefR.Mult Formalism.IndefR.Cx
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

theorem mem_of_mem_span_image {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] [AddCommGroup H]
    [Module ℂ H] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    (hj : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent ℂ fun k => j (b k))
    (N : Submodule K V) {z : V} (hz : j z ∈ Submodule.span ℂ (j '' (N : Set V))) : z ∈ N := by
  by_contra hn
  let b : Fin (Module.finrank K N) → V := fun k => (Module.finBasis K N k : V)
  have hb : LinearIndependent K b := (Module.finBasis K N).linearIndependent.map' N.subtype N.ker_subtype
  have hs : Submodule.span K (Set.range b) ≤ N := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (Module.finBasis K N k).2)
  have h1 := hj _ (Fin.cons z b) (linearIndependent_finCons.2 ⟨hb, fun h => hn (hs h)⟩)
  have h2 : (fun k => j ((Fin.cons z b : Fin (Module.finrank K N + 1) → V) k)) =
      (Fin.cons (j z) (fun k => j (b k)) : Fin (Module.finrank K N + 1) → H) := by
    funext k
    refine Fin.cases rfl (fun _ => rfl) k
  rw [h2, linearIndependent_finCons] at h1
  refine h1.2 (Submodule.span_le.2 ?_ hz)
  rintro _ ⟨x, hx, rfl⟩
  have h3 := congrArg (fun z : N => (z : V)) ((Module.finBasis K N).sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
  rw [← h3, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem exists_lvlE_eq {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ)
    (y : Fin (S.BaseDimension r X P ψ) → K) : ∃ x, (S.lvlE r P ψ).mulVecLin x = (S.V0E r X P ψ).mulVecLin y := by
  obtain ⟨u, hu⟩ := (image_idempotent_spec K _ (S.gaMat r (goodAt X P ψ))).2.le ⟨y, rfl⟩
  have h : S.gaMat r (goodAt X P ψ) = S.gaMat r (lvlIdem P ψ) * S.gaMat r (idemOf X) := by
    rw [← (group_action_matrix_hom K S G r).2, (idempotent_central K G X hX).2]
    rfl
  refine (image_idempotent_spec K _ (S.gaMat r (lvlIdem P ψ))).2.ge ⟨(S.gaMat r (idemOf X)).mulVec u, ?_⟩
  refine Eq.trans ?_ hu
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]

theorem goodFormsCoordinateMap_apply {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {Am : Formalism.L2.Indef.DefAmb Bs}
    (X : CxData Am) (b : Bool) (j : Bs.J) (c : Fin (X.dW b j) → ℂ) :
    X.w0C b j c = ∑ k, c k • X.eW b j (X.bW b j Bs.v0 k) := by
  show X.eW b j (∑ k, c k • X.bW b j Bs.v0 k) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul _ _ _

theorem goodFormsCoordinateMap_mem_of_lifts_mem {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {Am : Formalism.L2.Indef.DefAmb Bs}
    (X : CxData Am) {fc : Formalism.L2.Indef.DefSub Am → Formalism.L2.Indef.DefFace Bs} (cr : Crd Am fc) (b : Bool) (h5 : X.H5 cr b)
    (j : Bs.J) (t : Bs.Tup) (N : Submodule ℂ (X.W j)) (h : ∀ y, X.θ' j t (X.jL j t (cr.toL X.zs b j t y)) ∈ N)
    (c : Fin (X.dW b j) → ℂ) : X.w0C b j c ∈ N := by
  obtain ⟨d, hd⟩ := (h5 j t).2.ge ⟨c, rfl⟩
  rw [← hd]
  show ∑ k, d k • X.θ' j t (X.jL j t (cr.toL X.zs b j t (Pi.single k 1))) ∈ N
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h _)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem e_j_eOp (hU : R.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : Fin (R.nW i) → D.what₂.LL) :
    (R.HW i σ).e ((R.FW i).j σ ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y)) =
      postOn _ (R.eWf i σ) ((R.HW i σ).e ((R.FW i).j σ y)) := by
  have htw : ∀ g, (R.HW i σ).e ((R.FW i).j σ (GlobalTheory.LevelForms.twRep (R.FW i) g y)) =
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e ((R.FW i).j σ y)) := by
    intro g
    rw [GlobalTheory.LevelForms.twRep_apply, map_smulₛₗ, map_smul, (hU i σ).2.2, smul_smul, ← map_mul, Units.inv_mul, map_one,
      one_smul]
  rw [GlobalTheory.LevelForms.eOp_eq_sum, map_sum, map_sum]
  simp only [map_smulₛₗ, map_smul, htw]
  refine MultilinearMap.ext fun v => ?_
  simp only [RealDat.eWf, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply, postOn_apply, RingHom.id_apply]
  all_goals rfl

theorem exists_w0C_eq (i : Fin D.R.m) {w : (R.HW i (sg0 D A)).H} (h1 : w ∈ R.WS F false i (sg0 D A)) :
    ∃ c, Tw.out (s := twAt D.what₂.embLL A.v0) ((R.toCx F).w0C false i c) = w := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 h1
  have hs : ((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F) false)).ne'
  let c' : Fin ((R.toCx F).dW false i) → ℂ :=
    fun k => cj (twAt D.what₂.embLL A.v0) (c k * ((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ)⁻¹)
  have e1 := goodFormsCoordinateMap_apply (R.toCx F) false i c'
  refine ⟨c', (congrArg (Tw.out (s := twAt D.what₂.embLL A.v0)) e1).trans (Eq.trans ?_ hc)⟩
  show ∑ k, cj (twAt D.what₂.embLL A.v0) (c' k) • (((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) •
    R.bC F false i (sg0 D A) k) = _
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cj_cj, smul_smul, inv_mul_cancel_right₀ hs]

theorem exists_srcForm_eq (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (t : T0)
    (Z : Submodule D.what₂.LL (A.fam.L i t).S.Forms) (y : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) Z) → D.what₂.LL) :
    ∃ x, srcForm A i t F.P0 F.ψ0⁻¹ x = (A.fam.L i t).toF (A.fam.lvlA F.P0 F.ψ0) Z y := by
  obtain ⟨x, hx⟩ := exists_lvlE_eq (A.MtCSD i t) (A.leftGroupActionLift i t) A.X hX F.P0 F.ψ0⁻¹
    (((A.fam.L i t).zE (A.fam.lvlA F.P0 F.ψ0) Z).mulVecLin y)
  exact ⟨x, congrArg (fun u => (A.MtCSD i t).basis.equivFun.symm u) hx⟩

theorem out_lift_toL (i : Fin D.R.m) (t : T0)
    (y : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t)) → D.what₂.LL) :
    (R.toCx F).θ' i t ((R.toCx F).jL i t (F.cr.toL (R.toCx F).zs false i t y)) =
      Tw.mk (twAt D.what₂.embLL A.v0) (R.thG i t (jVx R i t
        ((A.fam.L i t).toF (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) y))) := rfl

theorem j_eOp_of_adForm (hW : R.models_HW) (hG : R.thP_thG) (hU : R.LUnif) (i : Fin D.R.m) (t : T0) (ph : ℂ)
    (y : Fin (R.nW i) → D.what₂.LL) (u : (R.HV i t).H) (h0 : adForm R i y = ph • R.thF i t u) :
    (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y) = ph • R.thG i t u := by
  have h1 := e_j_eOp R hU i (sg0 D A) y
  unfold adForm at h0
  rw [h0, LinearMap.map_smul, ← hG i t u, ← LinearMap.map_smul] at h1
  exact (hW i _).1 h1

end GlobalTheory.TraceIncl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableDescendOrbitSum
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2KernelIntegral

theorem integrable_descend_orbitSum {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] {h : G → ℂ} (hh : Integrable h μ) :
    Integrable (descend Γ (orbitSum Γ h)) (quotMeasure Γ μ) := by
  refine ⟨?_, ?_⟩
  · rw [aestronglyMeasurable_quotMeasure_iff_lift, (leftInv_orbitSum h).lift_descend]
    have hm : ∀ γ : Γ, AEMeasurable (fun x => h (γ * x)) μ := fun γ =>
      hh.1.aemeasurable.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving
    exact (AEMeasurable.tsum hm).aestronglyMeasurable
  · have h1 := lintegral_eq_lintegral_tsum (Γ := Γ) hh.1.enorm
    refine lt_of_le_of_lt ?_ (h1.symm.trans_lt hh.2)
    exact lintegral_mono fun q => enorm_tsum_le_tsum_enorm

theorem convR_eq_integral_kernelQ : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    ∀ f : G → ℂ, Continuous f → HasCompactSupport f → ∀ (F : L2 Γ μ) (x : G),
      Integrable (fun q => kernelQ Γ f (mk Γ x) q * F q) (quotMeasure Γ μ) ∧
        convR μ f (lift Γ F) x = ∫ q, kernelQ Γ f (mk Γ x) q * F q ∂quotMeasure Γ μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f hf hc F x
  have hf' : Continuous fun y => f (x⁻¹ * y) := hf.comp (continuous_const_mul _)
  have hc' : HasCompactSupport fun y => f (x⁻¹ * y) := hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  have hloc : LocallyIntegrable (lift Γ F) μ :=
    (locallyIntegrable_iff).2 fun C hC => (GlobalTheory.T.memLp_lift_L2DiscreteQuotient_on_compact G Γ μ F C hC).2
  have hi : Integrable (fun y => f (x⁻¹ * y) * lift Γ F y) μ :=
    hloc.integrable_smul_left_of_hasCompactSupport hf' hc'
  have key : descend Γ (orbitSum Γ fun y => f (x⁻¹ * y) * lift Γ F y) =
      fun q => kernelQ Γ f (mk Γ x) q * F q := by
    funext q
    induction q using Quotient.inductionOn with
    | h y =>
      refine ((leftInv_orbitSum _).descend_mk y).trans ?_
      change _ = kernelQ Γ f (mk Γ x) (mk Γ y) * F (mk Γ y)
      rw [kernelQ_mk, kernel_eq_orbitSum, orbitSum, orbitSum, ← tsum_mul_right]
      exact tsum_congr fun γ => congrArg (fun z => _ * F z) (mk_mul γ y)
  refine ⟨key ▸ integrable_descend_orbitSum hi, ?_⟩
  rw [convR_eq, integral_eq_integral_orbitSum (Γ := Γ) hi, key]

end GlobalTheory.AutomorphicL2KernelIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralEqSumOfSurjective
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassUnfold

theorem integral_eq_sum_of_surjective {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ]
    (π : G →* H) (hπ : Function.Surjective π) (J : Subgroup H) (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν)
    (ho : IsOpen (J.comap π : Set G)) (h1 : ν (J.comap π) = 1) (I : Type) [Fintype I] (y : I → H)
    (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (hf : ∀ c, Finite (Bridge.stab (π.comp Γ.subtype) J (y c)))
    (Φ : H → ℂ) (hΦ : ∀ (γ : Γ) h (k : J), Φ (π.comp Γ.subtype γ * h * k) = Φ h) :
    ∫ h in 𝓖, Φ (π h) ∂ν = ∑ c, (Nat.card (Bridge.stab (π.comp Γ.subtype) J (y c)) : ℂ)⁻¹ * Φ (y c) := by
  choose h hh using fun c => hπ (y c)
  have hS : ∀ c, {γ : G | γ ∈ Γ ∧ (h c)⁻¹ * γ * h c ∈ J.comap π} =
      Subtype.val '' (Bridge.stab (π.comp Γ.subtype) J (y c) : Set Γ) := by
    intro c
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, Bridge.mem_stab, Subgroup.mem_comap, map_mul,
      map_inv, hh]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨⟨γ, a⟩, b, rfl⟩
    · rintro ⟨δ, b, rfl⟩
      exact ⟨δ.2, b⟩
  have hfin : ∀ c, (Bridge.stab (π.comp Γ.subtype) J (y c) : Set Γ).Finite := fun c => hf c
  have key := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ (J.comap π) 𝓖 h𝓖 ho
    (by rw [h1]; exact ENNReal.one_ne_top) I h ?_ (fun c => by rw [hS]; exact (hfin c).image _)
    (fun x => Φ (π x)) ?_ ?_
  · rw [key.2.2, h1]
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hS, Set.ncard_image_of_injective _ Subtype.val_injective, hh]
    rfl
  · intro x
    refine (existsUnique_congr fun i => ?_).1 (hy (π x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, (γ * h i)⁻¹ * x, ?_, by group⟩
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, hh, e]
      change (π γ * y i)⁻¹ * (π γ * y i * k) ∈ J
      rw [inv_mul_cancel_left]
      exact k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, ⟨π k, hk⟩, by rw [map_mul, map_mul, hh]; rfl⟩
  · intro γ hγ x
    have := hΦ ⟨γ, hγ⟩ (π x) 1
    rw [OneMemClass.coe_one, mul_one] at this
    rw [map_mul]
    exact this
  · intro k hk x
    have := hΦ 1 (π x) ⟨π k, hk⟩
    rw [map_one, one_mul] at this
    rw [map_mul]
    exact this

theorem integral_eq_classSum : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), L.P.H = ⊥ → IsMeasDef V (lev D.sp.cm V.gram β L) μ 𝓕 → ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf V), Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y → (∀ c, Finite (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y c))) → ∀ Φ : Bridge.Gf V → ℂ, (∀ (γ : GQ V) h (k : (levEnv V β L).J), Φ (Bridge.ratF V γ * h * k) = Φ h) → ∫ h in 𝓕, Φ (fin V h) ∂μ = ∑ c, (Nat.card (Bridge.stab (Bridge.ratF V) (levEnv V β L).J (y c)) : ℂ)⁻¹ * Φ (y c) := by
  intro D V β L μ 𝓕 hL hμ I _ y hy hf Φ hΦ
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := hμ.1.1
  have hK : (levEnv V β L).J.comap (finHom V).rangeRestrict = (lev D.sp.cm V.gram β L).comap (finE V) := by
    ext g
    change (finE V g ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (finE V g) ∈ (⊥ : Subgroup _)) ↔
      (finE V g ∈ parLev D.sp.cm V.gram β L ∧ rTup β L (finE V g) ∈ L.P.H)
    rw [hL]
  refine integral_eq_sum_of_surjective μ (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective
    (levEnv V β L).J 𝓕 hμ.2 ?_ ?_ I y hy hf Φ hΦ
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level V β L] with κ hκ
    exact hκ.1
  · rw [hK]
    exact GlobalTheory.Mass.Levels.measure_comap_finE hμ.1

end GlobalTheory.ClassUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLatHatIffOfSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField GlobalTheory.SplitHecke
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicU.SplitFrame

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem map_map_sndA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (u : HeightOneSpectrum (𝓞 F))
    (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      compFin F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem vecLoc_finPart {n : ℕ} (u : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) (y : Fin n → AE D) :
    vecLoc u (fun i => finPart D (e * y i)) =
      compFin D.host.F D.host.E u e • fun i => compFin D.host.F D.host.E u (y i) :=
  funext fun i => (map_map_sndA u (e * y i)).trans ((compFin D.host.F D.host.E u).map_mul e (y i))

theorem compFin_eq_zero (he : IsSplitIdem D e) (hπ : Chart e v π) {u : HeightOneSpectrum (𝓞 D.host.F)}
    (hu : u ≠ v) : compFin D.host.F D.host.E u e = 0 := by
  obtain ⟨h1, h2, v', ε, ⟨α, rfl, -, ha⟩, hε⟩ := he
  have p1 : π e = 1 := by
    have := (hπ.2.1 (1 - e)).2 (by rw [mul_sub, mul_one, h1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have p2 : π (cA D e) = 0 := (hπ.2.1 _).2 h2
  have p3 : evalV D.host.F v α = 1 := by
    have := hπ.2.2.1 (pairA D.host.F 0 α)
    rw [← hε, map_add, p1, p2, add_zero] at this
    exact this.symm
  have hv : v = v' := by
    by_contra hne
    rw [ha v hne] at p3
    exact zero_ne_one p3
  subst hv
  have p4 : compFin D.host.F D.host.E u (e + cA D e) = 0 := by
    rw [hε]
    change (evalV D.host.F u α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [ha u hu, TensorProduct.zero_tmul]
  have p5 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [p5, map_mul, p4, mul_zero]

theorem mem_latHat_iff_of_support {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v)
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) {y : Fin n → Af F ⊗[F] E} {z : Fin n → Fv F v}
    (hv : vecLoc v y = splitIncl h τ z) (hu : ∀ u, u ≠ v → vecLoc u y = 0) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔ z ∈ splitLat τ L := by
  rw [mem_latHat_iff hL, ← splitIncl_mem_latLoc_iff h, ← hv]
  refine ⟨fun h => h v, fun h u => ?_⟩
  by_cases huv : u = v
  · subst huv; exact h
  · rw [hu u huv]; exact zero_mem _

theorem vecLoc_self (he : IsSplitIdem D e) (hπ : Chart e v π) {n : ℕ} (y : Fin n → AE D) :
    vecLoc v (fun i => finPart D (e * y i)) = splitIncl (isCMExt_host D) (chartEmb hπ) (fun k => π (y k)) := by
  have : (fun k => π (y k)) = splitVec (chartEmb hπ) (fun k => compFin D.host.F D.host.E v (y k)) :=
    funext fun k => chart_eq_splitProj hπ _
  rw [this, splitIncl_splitVec, vecLoc_finPart, compFin_eq_splitIdem he hπ]

theorem vecLoc_ne (he : IsSplitIdem D e) (hπ : Chart e v π) {n : ℕ} (y : Fin n → AE D)
    (u : HeightOneSpectrum (𝓞 D.host.F)) (hu : u ≠ v) : vecLoc u (fun i => finPart D (e * y i)) = 0 := by
  rw [vecLoc_finPart, compFin_eq_zero he hπ hu]
  exact funext fun i => zero_mul _

theorem lamHat_eq (V : HSp D) :
    LamHat V = Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) :=
  congrArg (Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E) (hermitianSpaceBaseLattice_eq_frameLattice V)

theorem mem_lamHat_iff (he : IsSplitIdem D e) (hπ : Chart e v π) (V : HSp D) (y : Fin V.rank → AE D) :
    (fun i => finPart D (e * y i)) ∈ LamHat V ↔ (fun k => π (y k)) ∈ splitLat (chartEmb hπ) (frameLat V) := by
  rw [lamHat_eq]
  exact mem_latHat_iff_of_support (isCMExt_host D) _ (frameLat_fg V) (vecLoc_self he hπ y) (vecLoc_ne he hπ y)

theorem frame_iff_isSplitBasis : ∀ {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v}, IsSplitIdem D e → ∀ (hπ : Chart e v π) (V : HSp D)
    (β : GL (Fin V.rank) (Fv D.host.F v)),
    Frame V e π β ↔ GlobalTheory.AdelicU.IsSplitBasis (GlobalTheory.AdelicU.chartEmb hπ) (GlobalTheory.AdelicU.frameLat V) β := by
  intro D e v π he hπ V β
  refine ⟨fun h u => ?_, fun h y => ?_⟩
  · choose y hy using fun k => hπ.1 ((β.1 *ᵥ u) k)
    have h1 := h y
    rw [mem_lamHat_iff he hπ, show (fun k => π (y k)) = β.1 *ᵥ u from funext hy, Matrix.mulVec_mulVec,
      Units.inv_mul, Matrix.one_mulVec] at h1
    simpa only [isInt_Ov] using h1.symm
  · rw [mem_lamHat_iff he hπ, h.mem_iff]
    simp only [isInt_Ov]

end GlobalTheory.AdelicU.SplitFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HLatMove

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mulVec_mem_hatL {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hx : x ∈ St β) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) : x.1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  obtain ⟨y, rfl⟩ := hx
  rw [hβ] at hz ⊢
  intro i
  have e : (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ z) = (intGL F E n y).1 *ᵥ ((β⁻¹).1 *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    change β⁻¹ * (β * intGL F E n y * β⁻¹) = _
    group
  rw [e]
  exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (y.1 i j).2 (hz j)

theorem mulVec_mem_hat {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) {q : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hq : Formalism.UG.bc (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom q ∈ St β)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) :
    q.1 *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have h := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _
    (mulVec_mem_hatL hβ hq (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
  convert h using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl

omit [NumberField F] [NumberField E] in

theorem bc_map_bc_inclR {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (g : GL (Fin n) E) :
    Formalism.UG.bc (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (Formalism.UG.bc (inclR (F := F) R) g) =
      Formalism.UG.bc (inclR (F := F) S) g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change Algebra.TensorProduct.map f (AlgHom.id F E) (1 ⊗ₜ g.1 i j) = 1 ⊗ₜ g.1 i j
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

omit [NumberField F] [NumberField E] in

theorem span_move {R O : Type} [CommRing R] [Algebra F R] [CommRing O] [Algebra O E] (H : AddSubgroup (Fin n → R ⊗[F] E))
    (g : GL (Fin n) E) (h q : GL (Fin n) (R ⊗[F] E)) (h1 : ∀ z ∈ H, q.1 *ᵥ z ∈ H) (h2 : ∀ z ∈ H, (q⁻¹).1 *ᵥ z ∈ H) :
    Submodule.span O {x : Fin n → E |
        ((Formalism.UG.bc (inclR (F := F) R) g * h * q)⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) ∈ H} =
      (Submodule.span O {x : Fin n → E | (h⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) ∈ H}).map
        ((Matrix.mulVecLin g.1).restrictScalars O) := by
  have hv : ∀ (g : GL (Fin n) E) (x : Fin n → E),
      (Formalism.UG.bc (inclR (F := F) R) g).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) = fun i => (1 : R) ⊗ₜ[F] (g.1 *ᵥ x) i := by
    intro g x
    funext i
    exact (RingHom.map_mulVec (inclR (F := F) R) g.1 x i).symm
  have key : ∀ z, (q⁻¹).1 *ᵥ z ∈ H ↔ z ∈ H := by
    refine fun z => ⟨fun hz => ?_, h2 z⟩
    have := h1 _ hz
    rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
  have hs : ∀ x : Fin n → E,
      ((Formalism.UG.bc (inclR (F := F) R) g * h * q)⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) =
        (q⁻¹).1 *ᵥ ((h⁻¹).1 *ᵥ fun i => (1 : R) ⊗ₜ[F] ((g⁻¹).1 *ᵥ x) i) := by
    intro x
    rw [← hv, map_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      mul_inv_rev, mul_inv_rev, mul_assoc]
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨(g⁻¹).1 *ᵥ x, (key _).1 (hs x ▸ hx), ?_⟩
    change g.1 *ᵥ ((g⁻¹).1 *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    change _ *ᵥ _ ∈ H
    rw [hs, key]
    change _ *ᵥ (fun i => (1 : R) ⊗ₜ[F] ((g⁻¹).1 *ᵥ (g.1 *ᵥ y)) i) ∈ H
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy

end General

variable {D : D7}

theorem exists_ratMat (V : HSp D) (γ : GQ V) : ∃ γE : GL (Fin V.rank) D.host.E, Bridge.IsRatMat V γ γE ∧
    (Bridge.ratF V γ).1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE := by
  obtain ⟨γE, -, hγ⟩ := γ.2
  have hm : matHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γE := hγ.symm
  refine ⟨γE, hm, ?_⟩
  change finHom V γ.1 = _
  rw [finHom, MonoidHom.comp_apply, hm]
  exact bc_map_bc_inclR _ _

theorem hLat_eq_span {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSDFrame V β Λ 1) (h : Bridge.Gf V) :
    Bridge.hLat V h = Submodule.span (𝓞 D.host.E) {x : Fin V.rank → D.host.E |
      (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
        GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))} := by
  rw [GlobalTheory.PrincInLevel.eq_latC hΛ, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
  rfl

theorem mulVec_mem_hat_swap {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : IsFrame β Λ) {q : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)} (hq : Formalism.UG.bc (swapAE D) q ∈ St β) :
    ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)),
      q.1 *ᵥ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) :=
  fun _ hz => mulVec_mem_hat hβ hq hz

theorem hLat_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSDFrame V β Λ 1) (g h q : Bridge.Gf V) (γE : GL (Fin V.rank) D.host.E)
    (hf : g.1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE) (hq : Formalism.UG.bc (swapAE D) q.1 ∈ St β) :
    Bridge.hLat V (g * h * q) = (Bridge.hLat V h).map ((Matrix.mulVecLin γE.1).restrictScalars (𝓞 D.host.E)) := by
  have hfr : IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hq' : Formalism.UG.bc (swapAE D) (q.1⁻¹) ∈ St β := by
    rw [MonoidHom.map_inv]; exact (St β).inv_mem hq
  have e : (g * h * q).1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE * h.1 * q.1 := hf ▸ rfl
  rw [hLat_eq_span hΛ, hLat_eq_span hΛ, e]
  exact span_move _ γE h.1 q.1 (mulVec_mem_hat_swap hfr hq) (mulVec_mem_hat_swap hfr hq')

theorem hLat_rat_mul_stab : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ γ : GQ V, ∃ γE : GL (Fin V.rank) D.host.E, Bridge.IsRatMat V γ γE ∧ ∀ h q : Bridge.Gf V, Formalism.UG.bc (swapAE D) (q : GL (Fin V.rank) _) ∈ St β → Bridge.hLat V (Bridge.ratF V γ * h * q) = Formalism.HermitianLatticesTheory.gmap ((Formalism.L2.Col.toGLm D.host.E V.rank).symm γE) (Bridge.hLat V h) := by
  intro D V β Λ hΛ γ
  obtain ⟨γE, hγ, hf⟩ := exists_ratMat V γ
  refine ⟨γE, hγ, fun h q hq => ?_⟩
  rw [Formalism.L2.Col.gmap_eq_map, MulEquiv.apply_symm_apply]
  exact hLat_mul hΛ _ h q γE hf hq

end GlobalTheory.HLatMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditive
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaCube

theorem cube_addInt_beBiadd : ∀ D : D7, GL3Theta.cube D ∧ GL3Theta.addInt D ∧ GL3Theta.beBiadd D := by
  intro D
  have hc : GL3Theta.cube D := Formalism.MainNotions.Ext.CutA.theorem_of_cube_of_addition_formulas D (GlobalTheory.T.sigmaStar_addition_formula_padic_modelParameter D) (GlobalTheory.T.pAdicFrobeniusStickelberger_of_d7_datum D)
  exact ⟨hc, Formalism.MainNotions.Ext.addInt_holds D, Formalism.MainNotions.Ext.beBiadd_of_cube D hc⟩

end GlobalTheory.ThetaCube
end

