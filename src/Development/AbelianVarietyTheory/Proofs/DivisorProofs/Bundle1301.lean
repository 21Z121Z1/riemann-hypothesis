import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCmFieldEqTwoMulTotallyRealSubfield
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.cm_finrank_eq_two_mul (D : D7) :
    Module.finrank ℚ D.host.E = Module.finrank ℚ D.host.F * 2 := by
  have h := (GlobalTheory.AdelicU.isCMExt_host D).2.2.1
  rw [← h]
  exact (Module.finrank_mul_finrank ℚ D.host.F D.host.E).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRestrictedProductEqProd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerAbs

open GlobalTheory.RestrMeas

theorem finsum_doubleCoset_restr {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X]
    [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v))
    (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (T : Subgroup X)
    (Tv : ∀ v, Subgroup (Y v)) (hT : ∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) (F : X → ℂ) (Fv : ∀ v, Y v → ℂ)
    (hF : ∀ x, F x = ∏ᶠ v, Fv v (pf v x))
    (hinv : ∀ v, ∀ t ∈ Tv v, ∀ y, ∀ k ∈ K v, Fv v (t * y * k) = Fv v y)
    (hfin : ∀ v, {q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)) | Fv v (Quotient.out q) ≠ 0}.Finite)
    (hev : ∀ᶠ v in cofinite, Fv v 1 = 1 ∧ ∀ y, Fv v y ≠ 0 → ∃ t ∈ Tv v, ∃ k ∈ K v, y = t * k) :
    ∑ᶠ q : DoubleCoset.Quotient (T : Set X) ((⨅ v, (K v).comap (pf v) : Subgroup X) : Set X), F (Quotient.out q) =
      ∏ᶠ v, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) := by
  set Kg : Subgroup X := ⨅ v, (K v).comap (pf v) with hKg
  have memKg : ∀ x, x ∈ Kg ↔ ∀ v, pf v x ∈ K v := fun x => by simp [hKg, Subgroup.mem_iInf]
  obtain ⟨S0, hS0⟩ := exists_finset_of_eventually hev

  have L0 : ∀ v (z₁ z₂ : Y v), DoubleCoset.mk (Tv v) (K v) z₁ = DoubleCoset.mk (Tv v) (K v) z₂ →
      Fv v z₁ = Fv v z₂ := fun v z₁ z₂ h => by
    obtain ⟨t, ht, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 h
    rw [e, hinv v t ht z₁ k hk]
  have L0' : ∀ v (z : Y v), Fv v (Quotient.out (DoubleCoset.mk (Tv v) (K v) z)) = Fv v z := fun v z =>
    L0 v _ _ (DoubleCoset.out_eq' _ _ _)

  have L1 : ∀ x y, DoubleCoset.mk T Kg x = DoubleCoset.mk T Kg y → ∀ v,
      DoubleCoset.mk (Tv v) (K v) (pf v x) = DoubleCoset.mk (Tv v) (K v) (pf v y) := fun x y h v => by
    obtain ⟨t, ht, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 h
    exact (DoubleCoset.eq _ _ _ _).2 ⟨pf v t, (hT t).1 ht v, pf v k, (memKg k).1 hk v, by rw [e]; simp⟩

  have L1' : ∀ x y, (∀ v, DoubleCoset.mk (Tv v) (K v) (pf v x) = DoubleCoset.mk (Tv v) (K v) (pf v y)) →
      DoubleCoset.mk T Kg x = DoubleCoset.mk T Kg y := fun x y h => by
    have h' := fun v => (DoubleCoset.eq _ _ _ _).1 (h v)
    choose t ht k hk e using h'
    let t' : ∀ v, Y v := fun v => if pf v x ∈ K v ∧ pf v y ∈ K v then 1 else t v
    have ht'T : ∀ v, t' v ∈ Tv v := fun v => by
      by_cases c : pf v x ∈ K v ∧ pf v y ∈ K v
      · simp only [t', if_pos c]; exact one_mem _
      · simp only [t', if_neg c]; exact ht v
    have ht'K : ∀ v, (pf v x)⁻¹ * (t' v)⁻¹ * pf v y ∈ K v := fun v => by
      by_cases c : pf v x ∈ K v ∧ pf v y ∈ K v
      · simp only [t', if_pos c, inv_one, mul_one]; exact mul_mem (inv_mem c.1) c.2
      · simp only [t', if_neg c]; rw [e v]; simpa [mul_assoc] using hk v
    have hev' : ∀ᶠ v in cofinite, t' v ∈ K v := ((hX.eventually_mem x).and (hX.eventually_mem y)).mono
      fun v c => by simp only [t', if_pos c]; exact one_mem _
    obtain ⟨g, -, hg⟩ := hX.exists_eq isEmptyElim t' hev'
    refine (DoubleCoset.eq _ _ _ _).2 ⟨g, (hT g).2 fun v => hg v ▸ ht'T v, x⁻¹ * g⁻¹ * y,
      (memKg _).2 fun v => by simpa [hg v] using ht'K v, by group⟩

  have ProjectionSandwichLength : ∀ x, (Function.mulSupport fun v => Fv v (pf v x)).Finite := fun x => by
    have hE : ∀ᶠ v in cofinite, pf v x ∈ K v ∧ v ∉ S0 :=
      (hX.eventually_mem x).and (eventually_of_finset S0 fun v hv => hv)
    refine (eventually_cofinite.1 hE).subset fun v hv c => hv ?_
    show Fv v (pf v x) = 1
    have := hinv v 1 (one_mem _) 1 (pf v x) c.1
    rw [one_mul, one_mul] at this
    rw [this, (hS0 v c.2).1]
  have L2 : ∀ x, F x ≠ 0 → ∀ v, Fv v (pf v x) ≠ 0 := fun x hx v h0 =>
    hx (by rw [hF]; exact finprod_eq_zero _ v h0 (ProjectionSandwichLength x))
  have KernelIndexFullLattice : ∀ v ∉ S0, ∀ y : Y v, Fv v y ≠ 0 → DoubleCoset.mk (Tv v) (K v) y = DoubleCoset.mk (Tv v) (K v) 1 ∧
      Fv v y = 1 := fun v hv y hy => by
    obtain ⟨t, ht, k, hk, e⟩ := (hS0 v hv).2 y hy
    refine ⟨((DoubleCoset.eq _ _ _ _).2 ⟨t, ht, k, hk, by rw [e, mul_one]⟩).symm, ?_⟩
    rw [e, ← (hS0 v hv).1, ← hinv v t ht 1 k hk, mul_one]
  have DegreeKernelLowerBound : ∀ x, (∀ v ∉ S0, Fv v (pf v x) ≠ 0) → F x = ∏ v ∈ S0, Fv v (pf v x) := fun x h => by
    rw [hF]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hS
    exact hv (KernelIndexFullLattice v hS _ (h v hS)).2

  have L3 : ∀ v ∉ S0, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) = 1 :=
    fun v hv => by
    rw [finsum_eq_single _ (DoubleCoset.mk (Tv v) (K v) 1), L0', (hS0 v hv).1]
    intro q hq
    by_contra h0
    apply hq
    rw [← DoubleCoset.out_eq' _ _ q]
    exact (KernelIndexFullLattice v hv _ h0).1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S0) fun v hv => by_contra fun h => hv (L3 v h),
    ← Finset.prod_coe_sort S0]
  let Q := fun v : S0 => DoubleCoset.Quotient (Tv v.1 : Set (Y v.1)) (K v.1 : Set (Y v.1))
  let Φ : DoubleCoset.Quotient (T : Set X) (Kg : Set X) → ∀ v : S0, Q v :=
    fun q v => DoubleCoset.mk (Tv v.1) (K v.1) (pf v.1 (Quotient.out q))
  let H : (∀ v : S0, Q v) → ℂ := fun b => ∏ v : S0, Fv v.1 (Quotient.out (b v))
  have hH : ∀ b, H b ≠ 0 → ∀ v : S0, Fv v.1 (Quotient.out (b v)) ≠ 0 := fun b hb v =>
    Finset.prod_ne_zero_iff.1 hb v (Finset.mem_univ _)
  have hval : ∀ q, F (Quotient.out q) ≠ 0 → F (Quotient.out q) = H (Φ q) := fun q hq => by
    rw [DegreeKernelLowerBound _ fun v _ => L2 _ hq v, ← Finset.prod_coe_sort S0]
    exact Finset.prod_congr rfl fun v _ => (L0' v.1 _).symm
  have hbij : Set.BijOn Φ (Function.support fun q => F (Quotient.out q)) (Function.support H) := by
    refine ⟨fun q hq => ?_, fun q₁ h₁ q₂ h₂ e => ?_, fun b hb => ?_⟩
    · show H (Φ q) ≠ 0
      rw [← hval q hq]; exact hq
    · rw [← DoubleCoset.out_eq' _ _ q₁, ← DoubleCoset.out_eq' _ _ q₂]
      refine L1' _ _ fun v => ?_
      by_cases hv : v ∈ S0
      · exact congrFun e ⟨v, hv⟩
      · rw [(KernelIndexFullLattice v hv _ (L2 _ h₁ v)).1, (KernelIndexFullLattice v hv _ (L2 _ h₂ v)).1]
    · have hb' := hH b hb
      let y : ∀ v, Y v := fun v => if h : v ∈ S0 then Quotient.out (b ⟨v, h⟩) else 1
      obtain ⟨x, -, hx⟩ := hX.exists_eq isEmptyElim y
        (eventually_of_finset S0 fun v hv => by simp only [y, dif_neg hv]; exact one_mem _)
      have hq := L1 _ _ (DoubleCoset.out_eq' T Kg (DoubleCoset.mk T Kg x))
      have hxS : ∀ v : S0, DoubleCoset.mk (Tv v.1) (K v.1) (pf v.1 x) = b v := fun v => by
        rw [hx, show y v.1 = Quotient.out (b v) by simp [y, v.2]]
        exact DoubleCoset.out_eq' _ _ _
      have hΦ : Φ (DoubleCoset.mk T Kg x) = b := funext fun v => (hq v.1).trans (hxS v)
      refine ⟨DoubleCoset.mk T Kg x, ?_, hΦ⟩
      show F _ ≠ 0
      have hne : ∀ v ∉ S0, Fv v (pf v (Quotient.out (DoubleCoset.mk T Kg x))) ≠ 0 := fun v hv => by
        rw [L0 v _ _ (hq v), hx]; simp only [y, dif_neg hv, (hS0 v hv).1]; exact one_ne_zero
      rw [DegreeKernelLowerBound _ hne, Finset.prod_ne_zero_iff]
      intro v hv
      rw [L0 v _ _ (hq v), hx]
      simp only [y, dif_pos hv]
      exact hb' ⟨v, hv⟩
  refine ((finsum_mem_support _).symm.trans ((finsum_mem_eq_of_bijOn Φ hbij fun q hq => hval q hq).trans
    (finsum_mem_support H))).trans ?_
  have hsum : ∀ v : S0, ∑ᶠ q : Q v, Fv v.1 (Quotient.out q) =
      ∑ q ∈ (hfin v.1).toFinset, Fv v.1 (Quotient.out q) := fun v =>
    finsum_eq_sum_of_support_subset _ fun q hq => (hfin v.1).mem_toFinset.2 hq
  rw [Finset.prod_congr rfl fun v _ => hsum v, Finset.prod_univ_sum]
  refine finsum_eq_sum_of_support_subset H fun b hb => ?_
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  exact fun v => by simpa using hH b hb v

end GlobalTheory.EulerAbs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumParabolicQuotientFubini
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem split_quotient_finsum_regroup : ∀ (P M N V : Type) [Group P] [Group M] [Group N] [AddCommMonoid V] (lev : P →* M) (s : M →* P) (u : N →* P), (∀ m, lev (s m) = m) → (∀ x, lev (u x) = 1) → Function.Injective u → (∀ p, lev p = 1 → ∃ x, u x = p) → ∀ (UP : Subgroup P) (UM : Subgroup M), UM.map s ≤ UP → UP.map lev ≤ UM → ∀ (Φ : P → V), (∀ p, ∀ q ∈ UP, Φ (p * q) = Φ p) → {q : P ⧸ UP | Φ q.out ≠ 0}.Finite → ∑ᶠ q : P ⧸ UP, Φ q.out = ∑ᶠ c : M ⧸ UM, ∑ᶠ x : N ⧸ UP.comap u, Φ (s c.out * u x.out) := by
  intro P M N V _ _ _ _ lev s u hsec hlu _hu_inj hker UP UM hsU hlevU Φ hΦ hfin
  let F : (M ⧸ UM) × (N ⧸ UP.comap u) → P ⧸ UP :=
    fun cx => (QuotientGroup.mk (s cx.1.out * u cx.2.out) : P ⧸ UP)
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨c, x⟩ ⟨c', x'⟩ h
      simp only [F] at h
      rw [QuotientGroup.eq] at h
      have h1 : (c.out)⁻¹ * c'.out ∈ UM := by
        have := hlevU (Subgroup.mem_map_of_mem lev h)
        simpa [map_mul, map_inv, hsec, hlu] using this
      have hc : c = c' := by
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
        exact QuotientGroup.eq.mpr h1
      subst hc
      have h2 : (x.out)⁻¹ * x'.out ∈ UP.comap u := by
        rw [Subgroup.mem_comap]
        have he : (s c.out * u x.out)⁻¹ * (s c.out * u x'.out) = u ((x.out)⁻¹ * x'.out) := by
          rw [map_mul, map_inv]; group
        rw [← he]; exact h
      have hx : x = x' := by
        rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
        exact QuotientGroup.eq.mpr h2
      rw [hx]
    · intro q
      set p := q.out with hp
      set c : M ⧸ UM := (QuotientGroup.mk (lev p) : M ⧸ UM) with hc
      have hk : (c.out)⁻¹ * lev p ∈ UM := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      set k := (c.out)⁻¹ * lev p with hkdef
      have hr : lev ((s c.out)⁻¹ * p * (s k)⁻¹) = 1 := by
        simp only [map_mul, map_inv, hsec, hkdef]; group
      obtain ⟨Z, hZ⟩ := hker _ hr
      refine ⟨(c, (QuotientGroup.mk Z : N ⧸ UP.comap u)), ?_⟩
      obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul (UP.comap u) Z
      simp only [F]
      rw [hy, ← QuotientGroup.out_eq' q, ← hp, QuotientGroup.eq]
      have hyU : u (y : N) ∈ UP := y.2
      have hsk : s k ∈ UP := hsU (Subgroup.mem_map_of_mem s hk)
      have he : (s c.out * u (Z * y))⁻¹ * p = (u (y : N))⁻¹ * s k := by
        rw [map_mul, hZ]; group
      rw [he]
      exact UP.mul_mem (UP.inv_mem hyU) hsk
  let e := Equiv.ofBijective F hbij
  have hval : ∀ cx, Φ (e cx).out = Φ (s cx.1.out * u cx.2.out) := by
    intro cx
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul UP (s cx.1.out * u cx.2.out)
    show Φ (F cx).out = _
    simp only [F]; rw [hh]; exact hΦ _ _ h.2
  have hsupp : (Function.support
      (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out))).Finite := by
    have : Function.support
        (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out))
        = e ⁻¹' {q : P ⧸ UP | Φ q.out ≠ 0} := by
      ext cx; simp only [Function.mem_support, Set.mem_preimage, Set.mem_setOf_eq, hval]
    rw [this]; exact hfin.preimage e.injective.injOn
  rw [← finsum_comp_equiv e]
  rw [finsum_congr hval]
  exact finsum_curry (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out)) hsupp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLeShiftOfSmallSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.FsTop

variable {X : Scheme.{0}} [IsIntegral X]

theorem regAt_mul' {x : X} {a b : X.functionField} (ha : RegAt x a) (hb : RegAt x b) : RegAt x (a * b) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  exact ⟨u * v, map_mul _ u v⟩

theorem regAt_inv_of_unitAt {x : X} {a : X.functionField} (ha : UnitAt x a) : RegAt x a⁻¹ := by
  obtain ⟨u, hu, rfl⟩ := ha
  refine ⟨(hu.unit⁻¹ : (X.presheaf.stalk x)ˣ), ?_⟩
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [← map_mul]
  simp

end GlobalTheory.HSNef.FsTop

open GlobalTheory.HSNef.FsTop in

theorem GlobalTheory.HSNef.le_shift_of_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M B : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → SmallFam B f w → Le M (B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl) := by
  intro k _ X _ p M B J _ f w hM hB
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hM
  obtain ⟨β, hβ, hbreg, hbnorm⟩ := hB
  have key : ∀ (x : X) (c : B.B.ι) (d : M.B.ι), x ∈ B.B.U c → x ∈ M.B.U d →
      RegAt x ((β c : X.functionField) / (ρ d : X.functionField)) := by
    intro x c d hc hd
    obtain ⟨l, hl⟩ := (hreg x d hd).2
    have hfl : f l ≠ 0 := fun h => hl.ne_zero (by rw [h, zero_mul])
    have e : (β c : X.functionField) / (ρ d) = (f l * β c) * (f l * ρ d)⁻¹ := by
      field_simp
    rw [e]
    exact regAt_mul' (hbreg x c hc l) (regAt_inv_of_unitAt hl)
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p _ M).2 ⟨β, ρ, hβ, hρ, fun x i j hi hj => key x i j hi hj, ?_⟩
  intro σ y i j hi hj
  have hxi : under y ∈ B.B.U i := mem_ptsIn.1 hi
  have hxj : under y ∈ M.B.U j := mem_ptsIn.1 hj
  have hq := key _ i j hxi hxj
  obtain ⟨l₀, hl₀⟩ := (hreg _ j hxj).2
  set q : X.functionField := (β i : X.functionField) / (ρ j : X.functionField) with hqdef
  have hval : ∀ l, ratVal (f l * (β i : X.functionField)) y = ratVal q y * ratVal (f l * (ρ j : X.functionField)) y := by
    intro l
    have e : f l * (β i : X.functionField) = q * (f l * (ρ j : X.functionField)) := by
      rw [hqdef]; field_simp
    rw [e, ratVal_mul hq ((hreg _ j hxj).1 l)]
  have hφj : (M.φ σ).φ j y = Real.log (∑ l, ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l)) :=
    hφ σ y j hj
  have hφi : ((B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl).φ σ).φ i y =
      (B.φ σ).φ i y + 2 * (Real.log (Fintype.card J) / 2) := rfl
  set S := ∑ l, ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l) with hS
  set φB := (B.φ σ).φ i y
  set Q := ‖ratVal q y‖
  have hn : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨l₀⟩
  have hSpos : 0 < S := by
    have h0 : 0 < ‖ratVal (f l₀ * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l₀) :=
      mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hl₀)) 2) (Real.exp_pos _)
    exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun l => ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
      (fun l _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (Finset.mem_univ l₀))

  have hterm : ∀ l, Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l)) ≤ Real.exp φB := by
    intro l
    have h1 := hbnorm σ y i hi l
    rw [hval l, norm_mul] at h1
    have h2 : Q * ‖ratVal (f l * (ρ j : X.functionField)) y‖ ≤ Real.exp (-w l) * Real.exp (φB / 2) := by
      have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (φB / 2)).le
      rwa [mul_assoc, ← Real.exp_add, show -φB / 2 + φB / 2 = 0 by ring, Real.exp_zero, mul_one] at this
    have h3 := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h2 2
    have e1 : (Real.exp (-w l) * Real.exp (φB / 2)) ^ 2 * Real.exp (2 * w l) = Real.exp φB := by
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1; push_cast; ring
    calc Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
        = (Q * ‖ratVal (f l * (ρ j : X.functionField)) y‖) ^ 2 * Real.exp (2 * w l) := by ring
      _ ≤ (Real.exp (-w l) * Real.exp (φB / 2)) ^ 2 * Real.exp (2 * w l) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp φB := e1
  have hsum : Q ^ 2 * S ≤ Fintype.card J * Real.exp φB := by
    rw [hS, Finset.mul_sum]
    calc ∑ l, Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
        ≤ ∑ _l : J, Real.exp φB := Finset.sum_le_sum fun l _ => hterm l
      _ = Fintype.card J * Real.exp φB := by simp
  rw [hφi, hφj]
  have hE : Real.exp (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2) ^ 2 =
      S / (Fintype.card J * Real.exp φB) := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2)
        = Real.log S - (Real.log (Fintype.card J) + φB) by push_cast; ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hSpos, Real.exp_log (by linarith)]
  have hpos : 0 ≤ Q * Real.exp (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2) :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine (pow_le_one_iff_of_nonneg hpos two_ne_zero).1 ?_
  rw [mul_pow, hE, ← mul_div_assoc, div_le_one (by positivity)]
  exact hsum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudySubfamilyLeShiftFubiniStudyFamily
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_ne_zero {x : X} {h : X.functionField} (hh : UnitAt x h) : h ≠ 0 := by
  obtain ⟨b, hb, rfl⟩ := hh
  intro e
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField (b * ↑hb.unit⁻¹) = 1 := by
    rw [IsUnit.mul_val_inv, map_one]
  rw [map_mul, e, zero_mul] at h1
  exact zero_ne_one h1

theorem regAt_div_unitAt {x : X} {g h : X.functionField} (hg : RegAt x g) (hh : UnitAt x h) :
    RegAt x (g / h) := by
  obtain ⟨a, ha⟩ := hg
  obtain ⟨b, hb, hbh⟩ := hh
  refine ⟨a * ↑hb.unit⁻¹, ?_⟩
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField b *
      algebraMap (X.presheaf.stalk x) X.functionField ↑hb.unit⁻¹ = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  rw [map_mul, ha, div_eq_mul_inv, ← hbh, eq_inv_of_mul_eq_one_right h1]

theorem le_shift_of_isFS_sub : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (M M' : HermLB p) (J J' : Type) [Fintype J] [Fintype J'] (f : J → X.functionField) (w : J → ℝ)
      (w' : J' → ℝ) (ι : J' → J) (Δ : ℝ), Function.Injective ι → IsFS M f w → IsFS M' (f ∘ ι) w' →
      (∀ j, w' j + Δ ≤ w (ι j)) → Le (M'.shift (fun _ => Δ) fun _ => rfl) M := by
  intro k _ X _ p M M' J J' _ _ f w w' ι Δ hι hM hM' hw
  rw [GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients]
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hM
  obtain ⟨ρ', hρ', hreg', hφ'⟩ := hM'
  simp only [Function.comp_apply] at hreg' hφ'

  have hq : ∀ (x : X) c d (j' : J'), UnitAt x (f (ι j') * (ρ' d : X.functionField)) →
      (ρ c : X.functionField) / (ρ' d : X.functionField) =
        f (ι j') * (ρ c : X.functionField) / (f (ι j') * (ρ' d : X.functionField)) := by
    intro x c d j' hu
    have hf : f (ι j') ≠ 0 := left_ne_zero_of_mul (unitAt_ne_zero hu)
    rw [mul_div_mul_left _ _ hf]
  have hτ : ∀ (x : X) c d, x ∈ M.B.U c → x ∈ M'.B.U d →
      RegAt x ((ρ c : X.functionField) / (ρ' d : X.functionField)) := by
    intro x c d hc hd
    obtain ⟨-, j', hj'⟩ := hreg' x d hd
    rw [hq x c d j' hj']
    exact regAt_div_unitAt ((hreg x c hc).1 (ι j')) hj'
  refine ⟨ρ, ρ', hρ, hρ', hτ, ?_⟩
  intro σ y c d hc hd
  have hc' := mem_ptsIn.1 hc
  have hd' := mem_ptsIn.1 hd
  set τ : X.functionField := (ρ c : X.functionField) / (ρ' d : X.functionField) with hτdef
  have hτr : RegAt (under y) τ := hτ _ c d hc' hd'

  have hval : ∀ j' : J', ratVal (f (ι j') * (ρ c : X.functionField)) y =
      ratVal τ y * ratVal (f (ι j') * (ρ' d : X.functionField)) y := by
    intro j'
    have e : f (ι j') * (ρ c : X.functionField) = τ * (f (ι j') * (ρ' d : X.functionField)) := by
      rw [hτdef]; field_simp
    rw [e, ratVal_mul hτr ((hreg' _ d hd').1 j')]
  set S : ℝ := ∑ j, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) with hS
  set S' : ℝ := ∑ j', ‖ratVal (f (ι j') * (ρ' d : X.functionField)) y‖ ^ 2 * Real.exp (2 * w' j') with hS'
  have e1 : (M.φ σ).φ c y = Real.log S := hφ σ y c hc
  have e2 : ((M'.shift (fun _ => Δ) fun _ => rfl).φ σ).φ d y = Real.log S' + 2 * Δ := by
    change (M'.φ σ).φ d y + 2 * Δ = _
    rw [hφ' σ y d hd]
  have hS'pos : 0 < S' := by
    obtain ⟨-, j₀, hj₀⟩ := hreg' _ d hd'
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨j₀, Finset.mem_univ _, ?_⟩
    have : ratVal (f (ι j₀) * (ρ' d : X.functionField)) y ≠ 0 := ratVal_ne_zero hj₀
    have : 0 < ‖ratVal (f (ι j₀) * (ρ' d : X.functionField)) y‖ := norm_pos_iff.2 this
    positivity
  set t : ℝ := ‖ratVal τ y‖ with ht
  have hineq : t ^ 2 * Real.exp (2 * Δ) * S' ≤ S := by
    classical
    calc t ^ 2 * Real.exp (2 * Δ) * S'
        = ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * (w' j' + Δ)) := by
          rw [hS', Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [hval, norm_mul, ← ht, mul_add, Real.exp_add]; ring
      _ ≤ ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w (ι j')) := by
          refine Finset.sum_le_sum fun j' _ => ?_
          gcongr
          exact hw j'
      _ = ∑ j ∈ Finset.univ.image ι, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) :=
          by rw [Finset.sum_image (fun a _ b _ h => hι h)]
      _ ≤ S := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => by positivity
  rw [e1, e2]
  have ht0 : 0 ≤ t := norm_nonneg _
  rcases ht0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact zero_le_one
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hineq
  have hE : Real.exp (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) ^ 2 = S' * Real.exp (2 * Δ) / S := by
    rw [← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) = (Real.log S' + 2 * Δ) - Real.log S := by
      push_cast; ring
    rw [this, Real.exp_sub, Real.exp_add, Real.exp_log hS'pos, Real.exp_log hSpos]
  rw [← sq_le_one_iff₀ (by positivity), mul_pow, hE]
  rw [← mul_div_assoc, div_le_one hSpos]
  linarith [hineq]

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricActionCoveringGroupOfCoreEquivarianceStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricAction_coveringGroup_of_core_equivariance : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → (∀ i σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → GeoAct T R κ v₀ := by
  first | exact @GlobalTheory.geoAct_of_eqAt | exact GlobalTheory.geoAct_of_eqAt | (intros; apply GlobalTheory.geoAct_of_eqAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1GrowthNoSectionsNefStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1_dim_bound_of_no_sections_nonneg_interNum : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → (∀ m : ℕ, 1 ≤ m → hdim k (twist F (lbPow L m)) 0 = 0) → 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) → (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 1 ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.noSection_H1_bound_riemann_roch | exact GlobalTheory.noSection_H1_bound_riemann_roch | (intros; apply GlobalTheory.noSection_H1_bound_riemann_roch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMuStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) → ℂ) (A : GLw a w) (B : GLw b w),
    A ∈ GlobalTheory.LFun.KGL w a → B ∈ GlobalTheory.LFun.KGL w b →
    hint (intMat a b w) (fun X => u (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X * B.val))) =
      hint (intMat a b w) u := by
  first | exact @GlobalTheory.BCT.HintInv.hint_intMat_mul_mul | exact GlobalTheory.BCT.HintInv.hint_intMat_mul_mul | (intros; apply GlobalTheory.BCT.HintInv.hint_intMat_mul_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlaceStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCompactSupport_twistedConstantTermSplitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w → HasCompactSupport f →
    HasCompactSupport (ctMu h w μ f) := by
  first | exact @GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split | exact GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split | (intros; apply GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split <;> assumption)
end

