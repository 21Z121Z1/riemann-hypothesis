import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0004

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.IntNumCompPerm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR

universe u v w

theorem intNum_comp_perm {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)) :
    intNum F P (bs ∘ σ) = intNum F P bs := by
  unfold intNum
  rw [FieldNumbers.mixedDiff_comp_perm]

theorem SymmStatement.of_type (F : Type u) [Field F] {K : Type} [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] : SymmStatement F ι := by
  classical
  intro I hI V n L σ hV
  have hA : ∀ L' : Fin n → K → ℤ, I V n L' = intNum F V L' := fun L' =>
    Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI V n L' hV
  rw [hA (L ∘ σ), hA L]
  exact intNum_comp_perm V L σ

theorem SymmStatement.of_found (hR : SymmRelabel.Statement.{u, v, w, 0, 0}) {K : Type v}
    [Fintype K] (F : Type u) [Field F] (ι : K → Type w) [∀ k, Fintype (ι k)] :
    SymmStatement F ι := by
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  refine hR F K ι (Fin (Fintype.card K)) (fun j => Fin (Fintype.card (ι (e.symm j)))) e
    (fun k => (Fintype.equivFin (ι k)).trans (finCongr ?_)) (SymmStatement.of_type F _)
  exact congrArg (fun x => Fintype.card (ι x)) (e.symm_apply_apply k).symm

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongWeightDiffLemmas
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

namespace LelongWeightDiff

variable {n d : ℕ}

theorem abs_half_log_sub_le {a ε κ : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hκ : 0 < κ) :
    |Real.log (a + ε * κ ^ 2) / 2 - Real.log (a + ε) / 2| ≤ |Real.log κ| := by
  have hb : 0 < a + ε := by linarith
  have hc : 0 < a + ε * κ ^ 2 := by positivity
  have hk2 : Real.log (κ ^ 2) = 2 * Real.log κ := by rw [Real.log_pow]; norm_num
  rcases le_total 1 κ with h1 | h1
  · have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ h1
    have l1 : Real.log (a + ε) ≤ Real.log (a + ε * κ ^ 2) := Real.log_le_log hb (by nlinarith)
    have l2 : Real.log (a + ε * κ ^ 2) ≤ Real.log (κ ^ 2) + Real.log (a + ε) := by
      rw [← Real.log_mul (by positivity) hb.ne']; exact Real.log_le_log hc (by nlinarith)
    rw [abs_of_nonneg (Real.log_nonneg h1), abs_le]; constructor <;> linarith
  · have hκ2 : κ ^ 2 ≤ 1 := pow_le_one₀ hκ.le h1
    have l1 : Real.log (a + ε * κ ^ 2) ≤ Real.log (a + ε) := Real.log_le_log hc (by nlinarith)
    have l2 : Real.log (κ ^ 2) + Real.log (a + ε) ≤ Real.log (a + ε * κ ^ 2) := by
      rw [← Real.log_mul (by positivity) hb.ne']; exact Real.log_le_log (by positivity) (by nlinarith)
    rw [abs_of_nonpos (Real.log_nonpos hκ.le h1), abs_le]; constructor <;> linarith

theorem exists_poly_of_linEval_eq_zero (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection J A) (u : Fin n → ℂ) (hu : linForm u ∉ J) :
    ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧
      ∀ x ∈ zeroSet J, linEval u x = 0 → eval (A *ᵥ x) P = 0 := by
  classical
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  have hs0 : Ideal.Quotient.mk J (linForm u) ≠ 0 := fun h => hu (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hex : ∃ m, ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g.Monic ∧ g.natDegree = m ∧
      Polynomial.aeval (Ideal.Quotient.mk J (linForm u)) g = 0 := by
    obtain ⟨g, hgm, -, hg⟩ := FibreBound.exists_monic_aeval_eq_zero J A hA (Ideal.Quotient.mk J (linForm u))
    exact ⟨_, g, hgm, rfl, hg⟩
  obtain ⟨g, hgm, hgd, hg⟩ := Nat.find_spec hex
  have hc : g.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr h0
    have hqm : q.Monic := Polynomial.monic_X.of_mul_monic_left hgm
    rw [map_mul, Polynomial.aeval_X] at hg
    refine Nat.find_min hex (m := q.natDegree) ?_ ⟨q, hqm, rfl, (mul_eq_zero.mp hg).resolve_left hs0⟩
    rw [← hgd, Polynomial.natDegree_mul Polynomial.X_ne_zero hqm.ne_zero, Polynomial.natDegree_X]
    omega
  refine ⟨g.coeff 0, hc, fun x hx hux => ?_⟩
  have hmem : Polynomial.eval₂ (pullback A).toRingHom (linForm u) g ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
    rw [Polynomial.aeval_def] at hg
    exact hg
  have h0 := hx _ hmem
  have hcomp : (eval x).comp (pullback A).toRingHom = eval (A *ᵥ x) :=
    RingHom.ext fun P => FibreBound.eval_pullback A x P
  have hl : eval x (linForm u) = linEval u x := by simp [linForm, linEval]
  rwa [Polynomial.hom_eval₂, hcomp, hl, hux, Polynomial.eval₂_at_zero] at h0

theorem measurable_chartDens {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f : (Fin n → ℂ) → ℝ} {ψ : Fin d → (Fin n → ℂ) → ℝ} (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hA : IsFiniteProjection J A)
    (hf : ContinuousOn f (zeroSet J)) (hψ : ∀ i, SmoothNear (zeroSet J) (ψ i)) :
    Measurable (chartDens J A f ψ) := by
  classical
  rw [CutOffDominated.chartDens_congr_zeroSet (g := (zeroSet J).piecewise f 0)
    (fun x hx => (Set.piecewise_eq_of_mem _ _ _ hx).symm)]
  exact (SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA
    (hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet) hψ).1

theorem abs_chartDens_le {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    |chartDens J A f ψ y| ≤ chartAbsDens J A f ψ y := by
  classical
  unfold chartDens chartAbsDens
  simp only [CutOffDominated.sheetSum_eq_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs <;> simp

theorem chartDens_sub {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (f f' : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    chartDens J A f ψ y - chartDens J A f' ψ y = chartDens J A (fun x => f x - f' x) ψ y := by
  classical
  unfold chartDens
  simp only [CutOffDominated.sheetSum_eq_sum _ hfin, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem tendsto_finset_sum_zero {ι α : Type*} {l : Filter α} (s : Finset ι) (f : ι → α → ℝ)
    (h : ∀ i ∈ s, Tendsto (f i) l (𝓝 0)) : Tendsto (fun a => ∑ i ∈ s, f i a) l (𝓝 0) := by
  simpa using tendsto_finsetSum s h

end LelongWeightDiff

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongWeightLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix Set
open scoped ContDiff Manifold
open GroundTheory.Heights₂.Heights (varInt chartInt SmoothNear localMult linEval linForm logReg contDiff_linEval
  contDiff_logReg smoothNear_of_contDiff)

namespace LelongWeightLimit

variable {n : ℕ}

theorem exists_contDiff_eqOn {Z : Set (Fin n → ℂ)} (hZ : IsClosed Z) {f : (Fin n → ℂ) → ℝ}
    (hf : SmoothNear Z f) (hfc : HasCompactSupport f) :
    ∃ g : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ Z, g x = f x := by
  obtain ⟨U, hU, hZU, hfU⟩ := hf
  have hK : IsCompact (Z ∩ tsupport f) := hfc.isCompact.inter_left hZ
  obtain ⟨V, hV, hKV, hVU, -⟩ :=
    exists_open_between_and_isCompact_closure hK hU (inter_subset_left.trans hZU)
  obtain ⟨θ, hθ, -, hθs, hθ1⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, Fin n → ℂ) (n := ⊤) hV hK.isClosed hKV
  rw [contMDiff_iff_contDiff] at hθ
  refine ⟨θ * f, ?_, hfc.mul_left, fun x hx => ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hx : x ∈ U
    · exact hθ.contDiffAt.mul (hfU.contDiffAt (hU.mem_nhds hx))
    · have hev : θ * f =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds fun h => hx (hVU h)] with y hy
        have : θ y = 0 := by
          by_contra h
          exact hy (subset_closure (hθs ▸ (Function.mem_support.mpr h)))
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · by_cases hxf : x ∈ tsupport f
    · rw [Pi.mul_apply, (hθ1 x).1 ⟨hx, hxf⟩, one_mul]
    · rw [Pi.mul_apply, image_eq_zero_of_notMem_tsupport hxf, mul_zero]

theorem varInt_congr {J : Ideal (MvPolynomial (Fin n) ℂ)} {d : ℕ} {f g : (Fin n → ℂ) → ℝ}
    (h : ∀ x ∈ ComplexSets.zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    varInt J d f φ = varInt J d g φ := by
  unfold varInt chartInt
  split_ifs
  · rw [CutOffDominated.chartDens_congr_zeroSet h]
  · rfl

theorem smoothNear_weight {Z : Set (Fin n → ℂ)} (u : Fin n → ℂ) {k : (Fin n → ℂ) → ℝ}
    (hk : SmoothNear Z k) (hk0 : ∀ x ∈ Z, 0 < k x) {ε : ℝ} (hε : 0 < ε) :
    SmoothNear Z (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) := by
  obtain ⟨U, hU, hZU, hkU⟩ := hk
  refine ⟨U ∩ k ⁻¹' Ioi 0, hkU.continuousOn.isOpen_inter_preimage hU isOpen_Ioi,
    fun x hx => ⟨hZU hx, hk0 x hx⟩, ?_⟩
  refine ContDiffOn.div_const (ContDiffOn.log ?_ fun x hx => ?_) _
  · exact ((contDiff_norm_sq ℝ).comp (contDiff_linEval u)).contDiffOn.add
      (contDiffOn_const.mul ((hkU.mono inter_subset_left).pow 2))
  · have h1 : 0 < ε * k x ^ 2 := mul_pos hε (pow_pos hx.2 2)
    have h2 : 0 ≤ ‖linEval u x‖ ^ 2 := sq_nonneg _
    exact (by linarith : (0 : ℝ) < ‖linEval u x‖ ^ 2 + ε * k x ^ 2).ne'

end LelongWeightLimit

open LelongWeightLimit in

theorem LelongWeightLimit.proof (hL : GroundTheory.Heights₂.Heights.LelongLimit.Statement)
    (hS : GroundTheory.Heights₂.Heights.StokesOnVariety.Statement) (hD : LelongWeightDiff.Statement) :
    LelongWeightLimit.Statement := by
  intro n d J u f k φ hJ hdim hu hf hfc hφ hk hk0
  obtain ⟨g, hg, hgc, hgf⟩ :=
    exists_contDiff_eqOn (GroundTheory.Heights₂.Heights.SheetSumMeasurable.isClosed_zeroSet J) hf hfc
  have hsum : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) =
      ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ := by
    refine finsum_congr fun W => finsum_congr fun hW => ?_
    rw [varInt_congr (fun x hx => hgf x fun q hq => hx q (le_sup_left.trans hW.1.2 hq)) φ]
  have hlim := (hL n d J u g φ hJ hdim hu hg hgc hφ).add (hD n d J u g k φ hJ hdim hu hg hgc hφ hk hk0)
  rw [hsum, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [varInt_congr (fun x hx => (hgf x hx).symm) (vecCons _ φ),
    hS n d J g _ φ hJ hdim (smoothNear_of_contDiff hg) (smoothNear_weight u hk hk0 hε) hφ (Or.inl hgc),
    hS n d J g (logReg u ε) φ hJ hdim (smoothNear_of_contDiff hg)
      (smoothNear_of_contDiff (contDiff_logReg u hε)) hφ (Or.inl hgc)]
  ring

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

universe u

namespace ProjContract

theorem finsum_mul_eq_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

section Theory

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

omit [DecidableEq K] in

theorem ratDiv_eq (P : Ideal (NumbersDVR.MRing ι F)) (f g : NumbersDVR.MRing ι F)
    (W : Ideal (NumbersDVR.MRing ι F)) :
    NumbersDVR.ratDiv P f g W = AI.I1.ratDiv P f g W := by
  simp only [NumbersDVR.ratDiv, AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
  rw [Bridge.divCycle_eq, Bridge.divCycle_eq]

theorem isIntersectionTheory (I : AI.I1.IFamily F ι) (hI : AI.I1.IsFieldIntersection I) :
    FieldNumbers.IsIntersectionTheory F I where
  base P hP h0 := by
    choose i hi using hP.relevant
    have hd := (FieldNumbers.relDim_eq_iff_hasRelDim P 0).mp h0
    have hV : AI.I1.IsProjVarF P 0 := ⟨(Bridge.isMultiProjPrime_iff P).mp hP, hd⟩
    have h1 := hI.1 P ![] i hV hi
    have h2 := NumbersDVR.IntNumPoint.proof FieldNumbers.IntNumBase.full F K ι P i hP hd hi
    have h3 := (FieldNumbers.IntNumBase.full F K ι P hP h0).2
    have h4 : FieldNumbers.resDeg P = Module.finrank F
        (@FieldNumbers.homFracDegZero _ _ _ _ _ P hP.isPrime) := by
      rw [FieldNumbers.resDeg, dif_pos hP.isPrime]
    rw [h1, ← h2, h3, h4]
  cut P n hP hn bf bg f g hf hg hfP hgP bs := by
    have hd := (FieldNumbers.relDim_eq_iff_hasRelDim P (n + 1)).mp hn
    rw [hI.2 P n bs _ f g ⟨(Bridge.isMultiProjPrime_iff P).mp hP, hd⟩
      ⟨bf, bg, (Bridge.isMultiHomog_iff f bf).mp hf, (Bridge.isMultiHomog_iff g bg).mp hg, hfP, hgP,
        fun k => rfl⟩]
    simp only [NumbersDVR.cycEval, AI.I1.cycEval, ratDiv_eq]
    exact (finsum_mul_eq_sum _ _).symm

end Theory

section Image

variable {F : Type u} [Field F] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

def emb (hv : AI.I1.IsBlockMap κ v) : K ↪ K' := ⟨κ, hv.1⟩

theorem range_eq (hv : AI.I1.IsBlockMap κ v) :
    Set.range v = Set.range (FieldNumbers.blockIncl (emb hv) ι') := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    have h := hv.2.2.1 p
    revert h
    generalize v p = q
    obtain ⟨a, b⟩ := q
    rintro (rfl : a = κ p.1)
    exact ⟨⟨p.1, b⟩, rfl⟩
  · rintro ⟨⟨k, x⟩, rfl⟩
    exact hv.2.2.2 _ ⟨k, rfl⟩

def blockEquiv (hv : AI.I1.IsBlockMap κ v) : (Σ k, ι k) ≃ (Σ k, ι' (emb hv k)) :=
  (Equiv.ofInjective v hv.2.1).trans ((Equiv.setCongr (range_eq hv)).trans
    (Equiv.ofInjective _ (FieldNumbers.PFContracted.blockIncl_injective_of_embedding (emb hv) ι')).symm)

theorem blockIncl_blockEquiv (hv : AI.I1.IsBlockMap κ v) (p : Σ k, ι k) :
    FieldNumbers.blockIncl (emb hv) ι' (blockEquiv hv p) = v p := by
  simp [blockEquiv, Equiv.apply_ofInjective_symm]

theorem imageVar_eq (hv : AI.I1.IsBlockMap κ v) (V' : Ideal (Geo.MRingOver F ι')) :
    AI.I1.imageVar F v V' = (FieldNumbers.contractPrime (emb hv) V').comap
      (rename (blockEquiv hv) : Geo.MRingOver F ι →ₐ[F] _).toRingHom := by
  ext x
  simp only [AI.I1.imageVar, FieldNumbers.contractPrime, Ideal.mem_comap, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, rename_rename]
  have : (FieldNumbers.blockIncl (emb hv) ι' ∘ blockEquiv hv) = v := funext (blockIncl_blockEquiv hv)
  rw [this]

theorem ringKrullDim_imageVar (hv : AI.I1.IsBlockMap κ v) (V' : Ideal (Geo.MRingOver F ι')) :
    ringKrullDim (Geo.MRingOver F ι ⧸ AI.I1.imageVar F v V') =
      ringKrullDim (NumbersDVR.MRing (fun k => ι' (emb hv k)) F ⧸
        FieldNumbers.contractPrime (emb hv) V') := by
  rw [imageVar_eq hv]
  set J := FieldNumbers.contractPrime (emb hv) V'
  let e := (renameEquiv F (blockEquiv hv)).toRingEquiv
  refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ J e ?_)
  exact (Ideal.map_comap_of_surjective _ e.surjective J).symm

end Image

end ProjContract

open ProjContract in

theorem ProjContract.full :
    ∀ (F : Type u) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.ProjContractStatement F ι ι' := by
  intro F _ K _ ι _ K' _ ι' _
  classical
  intro I' hI' κ v V' e d L hv hV' hVd hde
  have hrel : FieldNumbers.relDim V' = e := (FieldNumbers.relDim_eq_iff_hasRelDim V' e).mpr hV'.2
  have hV'f : NumbersDVR.IsMultiProjPrime V' := (Bridge.isMultiProjPrime_iff V').mpr hV'.1
  rw [FieldNumbers.IntNumUnique.full F K' ι' I' (isIntersectionTheory I' hI') V' hV'f e hrel]
  have hc : FieldNumbers.relDim (FieldNumbers.contractPrime (emb hv) V') = d := by
    refine (FieldNumbers.relDim_eq_iff_hasRelDim _ d).mpr ?_
    show ringKrullDim _ = _
    rw [← ringKrullDim_imageVar hv]
    exact hVd.2
  exact FieldNumbers.ProjectionFormulaContracted.full F K K' (emb hv) ι' V' hV'f e hrel
    (lt_of_eq_of_lt hc (FieldNumbers.PFContracted.natCast_lt_withBotWithTop hde)) L

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

section Relabel

variable {K K' : Type} {ι : K → Type} {ι' : K' → Type} {κ : K → K'}
  {v : (Σ k, ι k) → (Σ k', ι' k')}

def blockVar (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) (p : Σ k, ι k) : Σ k, ι' (κ k) :=
  ⟨p.1, cast (congrArg ι' (hb.2.2.1 p)) (v p).2⟩

theorem blockIncl_blockVar (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) (p : Σ k, ι k) :
    blockIncl ⟨κ, hb.1⟩ ι' (blockVar hb p) = v p := by
  refine Sigma.ext (hb.2.2.1 p).symm ?_
  exact (cast_heq _ _)

def blockVarEquiv (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) : (Σ k, ι k) ≃ (Σ k, ι' (κ k)) :=
  Equiv.ofBijective (blockVar hb) (by
    have hI : Function.Injective (blockIncl ⟨κ, hb.1⟩ ι') := by
      rintro ⟨a, x⟩ ⟨b, y⟩ h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      cases hb.1 h1
      cases eq_of_heq h2
      rfl
    refine ⟨fun p q h => hb.2.1 ?_, fun ⟨k, a⟩ => ?_⟩
    · rw [← blockIncl_blockVar hb p, ← blockIncl_blockVar hb q, h]
    · obtain ⟨p, hp⟩ := hb.2.2.2 ⟨κ k, a⟩ ⟨k, rfl⟩
      exact ⟨p, hI ((blockIncl_blockVar hb p).trans hp)⟩)

theorem imageVar_eq_comap {F : Type u} [Field F] (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v)
    (V' : Ideal (MRing ι' F)) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.imageVar F v V' =
      (contractPrime ⟨κ, hb.1⟩ V').comap (rename (blockVarEquiv hb)) := by
  ext f
  unfold ReciprocityTheory.ChartRestriction.G.AI.I1.imageVar contractPrime
  simp only [Ideal.mem_comap]
  have hfun : (blockIncl ⟨κ, hb.1⟩ ι' ∘ blockVarEquiv hb) = v := funext (blockIncl_blockVar hb)
  have e : rename (blockIncl ⟨κ, hb.1⟩ ι') (rename (blockVarEquiv hb) f) = rename v f := by
    rw [rename_rename, hfun]
  exact iff_of_eq (congrArg (· ∈ V') e.symm)

end Relabel

theorem ProjDeg.of_found (hPF : ProjectionFormulaDegree.Statement.{u})
    (hFn : FnDegRelDeg.Statement.{u}) {K K' : Type} [Fintype K] [Fintype K'] (F : Type u) [Field F]
    (ι : K → Type) [∀ k, Fintype (ι k)] (ι' : K' → Type) [∀ k, Fintype (ι' k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι' := by
  classical
  intro I I' hI hI' κ v V' e L i' hb hV' hV hc
  have hA' := Numbers.agree_of IntNumBase.full CutRational.full ExistsForm.full
    DivCycleSupport.full I' hI' V' e (fun j => ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg κ (L j)) hV'
  have hA := Numbers.agree_of IntNumBase.full CutRational.full ExistsForm.full
    DivCycleSupport.full I hI _ e L hV
  rw [hA', hA]
  set j : K ↪ K' := ⟨κ, hb.1⟩
  have hP' : IsMultiProjPrime V' := (Objects.isMultiProjPrime_iff V').mpr hV'.1
  have := hP'.isPrime
  have himg := imageVar_eq_comap (F := F) hb V'

  have hRen := RenameIntNum.full F K K (fun k => ι k) (fun k => ι' (κ k)) (Equiv.refl K)
    (blockVarEquiv hb) (fun _ => rfl) (contractPrime j V') e L
  have hdimP : relDim (contractPrime j V') = (e : WithBot (WithTop ℤ)) := by
    refine relDim_eq_of_ringKrullDim _ e ?_
    have eq : MRing ι F ⧸ (contractPrime j V').comap (rename (blockVarEquiv hb)) ≃+*
        MRing (fun k => ι' (κ k)) F ⧸ contractPrime j V' :=
      Ideal.quotientEquiv _ _ (renameEquiv F (blockVarEquiv hb)).toRingEquiv
        (Ideal.map_comap_of_surjective _ (renameEquiv F (blockVarEquiv hb)).surjective _).symm
    have h2 : ringKrullDim (MRing ι F ⧸ (contractPrime j V').comap (rename (blockVarEquiv hb))) =
        ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← himg]
      exact hV.2
    exact (ringKrullDim_eq_of_ringEquiv eq).symm.trans h2
  obtain ⟨-, hPFe⟩ := hPF F K K' j ι' V' hP' e (relDim_eq_of_ringKrullDim V' e hV'.2) hdimP L
  have hfn := hFn F K K' ι ι' κ v hb V' hP' i' hc
  rw [himg, hRen, hfn]
  exact hPFe

end

end GroundTheory.Heights₂.Heights.Targets
end

