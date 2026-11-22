import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
variable {m l n : Type*} [Fintype m] [Fintype l] [Fintype n]
  [DecidableEq m] [DecidableEq l] [DecidableEq n]

def SameJet {k : Type*} (u u' : V → k → ℂ) (z : V) : Prop :=
  ∀ a, u z a = u' z a ∧ ∃ D : V →L[ℝ] ℂ,
    HasFDerivAt (fun x => u x a) D z ∧ HasFDerivAt (fun x => u' x a) D z

section Jet

variable {k : Type*} {u u' v v' : V → k → ℂ} {z : V}

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem SameJet.val (h : SameJet u u' z) : u z = u' z := funext fun a => (h a).1

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem SameJet.add (h : SameJet u u' z) (h' : SameJet v v' z) :
    SameJet (fun x => u x + v x) (fun x => u' x + v' x) z := fun a => by
  obtain ⟨e, D, h1, h2⟩ := h a
  obtain ⟨e', D', h1', h2'⟩ := h' a
  exact ⟨by simp [e, e'], D + D', h1.add h1', h2.add h2'⟩

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem SameJet.mulVec [Fintype k] {p : Type*} {M : V → Matrix p k ℂ} (hM : MContDiffAt 1 M z)
    (h : SameJet u u' z) : SameJet (fun x => M x *ᵥ u x) (fun x => M x *ᵥ u' x) z := fun a => by
  choose e D h1 h2 using h
  refine ⟨by simp [Matrix.mulVec, dotProduct, e],
    ∑ b, (M z a b • D b + u' z b • fderiv ℝ (fun x => M x a b) z), ?_, ?_⟩
  · simp only [← e]
    exact HasFDerivAt.fun_sum fun b _ => (hM.diff a b).hasFDerivAt.mul (h1 b)
  · exact HasFDerivAt.fun_sum fun b _ => (hM.diff a b).hasFDerivAt.mul (h2 b)

theorem SameJet.covDel [Fintype k] [DecidableEq k] (h : SameJet u u' z) (K : V → Matrix k k ℂ)
    (ξ : V) : covDel K u z ξ = covDel K u' z ξ := by
  rw [HermFrame.covDel, HermFrame.covDel, h.val]
  congr 1
  funext a
  obtain ⟨-, D, h1, h2⟩ := h a
  rw [del_eq_of_hasFDerivAt h1, del_eq_of_hasFDerivAt h2]

theorem SameJet.secDbar (h : SameJet u u' z) (ξ : V) :
    HermitianCurvatureForms.secDbar u z ξ = HermitianCurvatureForms.secDbar u' z ξ := by
  funext a
  obtain ⟨-, D, h1, h2⟩ := h a
  rw [HermitianCurvatureForms.secDbar, HermitianCurvatureForms.secDbar, dbar_eq_of_hasFDerivAt h1, dbar_eq_of_hasFDerivAt h2]

end Jet

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem mContDiffAt_orthLift {k : WithTop ℕ∞} (h : MContDiffAt k H z)
    (hs : IsUnit (subGram (H z)).det) : MContDiffAt k (fun x => orthLift (H x)) z := by
  have hc : MContDiffAt k (fun x => orthCoeff (H x)) z :=
    (h.subGram.transpose.inv (by rwa [det_transpose])).mul (h.submatrix Sum.inr Sum.inl).transpose
  rintro (a | a) b
  exacts [hc.neg a b, contDiffAt_const]

theorem trace_eq_blocks (K T : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    T.trace = (blockSS K T).trace + (blockQQ K T).trace := by
  rw [blockSS, blockQQ, trace_mul_cycle, trace_mul_cycle (quotMap m l), ← trace_add,
    ← Matrix.add_mul, incl_mul_orthProj_add, Matrix.one_mul]

def BodyA (U : Set V) (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) : Prop :=
  (IsHermFrame U H → (∀ z ∈ U, IsUnit (subGram (H z)).det) →
    IsHermFrame U (HermitianCurvatureForms.gramS H) ∧ IsHermFrame U (HermitianCurvatureForms.gramQ H) ∧
      ∀ z ∈ U, HermitianCurvatureForms.SubQuotAt H z) ∧
  (IsPosFrame U H →
    IsPosFrame U (HermitianCurvatureForms.gramS H) ∧ IsPosFrame U (HermitianCurvatureForms.gramQ H) ∧
    (∀ z ∈ U, HermitianCurvatureForms.SecondFormSignAt H z ∧ HermitianCurvatureForms.ExtBlocksAt H z ∧ HermitianCurvatureForms.AnyRankAt H z) ∧
    (Fintype.card m = 1 → Fintype.card l = 1 → ∀ z ∈ U, HermitianCurvatureForms.RankTwoAt H z))

def BodyB (U : Set V) (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) : Prop :=
  (IsHermFrame U H → (∀ z ∈ U, IsUnit (CovariantDbarLeibniz.subField H z).det) →
    IsHermFrame U (CovariantDbarLeibniz.subField H) ∧ IsHermFrame U (CovariantDbarLeibniz.quotField H) ∧
      ∀ z ∈ U, CovariantDbarLeibniz.SubQuotAt H z) ∧
  (∀ [Unique m] [Unique l], IsPosFrame U H →
    ∀ z ∈ U, CovariantDbarLeibniz.ExtBlocksAt H z ∧ CovariantDbarLeibniz.RankTwoAt H z) ∧
  (IsPosFrame U H → ∀ z ∈ U, CovariantDbarLeibniz.ExtBlocksAt H z ∧ CovariantDbarLeibniz.ChTwoAt H z)

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem isUnit_sub (h : IsPosFrame U H) (z : V) (hz : z ∈ U) : IsUnit (subGram (H z)).det :=
  h.sub.isHermFrame.isUnit z hz

section Pull

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
  [IsScalarTower ℝ ℂ W] (L : W →L[ℂ] V) {w : W}

variable {K : V → Matrix n n ℂ}

variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det)
include h

include hs

end Pull

section Smooth

variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) (hz : z ∈ U)
include h hs hz

omit hs in

theorem smooth_secondForm (ξ : V) : MContDiffAt ∞ (fun x => secondForm H x ξ) z :=
  ((mContDiffAt_const _).mul ((h.mContDiffAt hz).conn (h.isUnit z hz) le_rfl ξ)).mul
    (mContDiffAt_const _)

theorem smooth_secondFormAdj (ξ : V) : MContDiffAt ∞ (fun x => secondFormAdj H x ξ) z :=
  ((((h.sub hs).mContDiffAt hz).transpose.inv (by rw [det_transpose]; exact hs z hz)).mul
    (smooth_secondForm h hz ξ).conjTranspose).mul ((h.quot hs).mContDiffAt hz).transpose

theorem smooth_extForm (ξ : V) : MContDiffAt ∞ (fun x => extForm H x ξ) z := by
  have hl := mContDiffAt_orthLift (h.mContDiffAt hz) (hs z hz)
  simp only [extForm_eq_neg_mdbar]
  have hc : MContDiffAt ∞ (fun x => orthCoeff (H x)) z := fun a b => by
    simpa [orthLift] using hl.neg (.inl a) b
  exact (hc.mdbar le_rfl ξ).neg

theorem smooth_extFormAdj (ξ : V) : MContDiffAt ∞ (fun x => extFormAdj H x ξ) z :=
  ((((h.quot hs).mContDiffAt hz).transpose.inv
    (by rw [det_transpose]; exact (h.quot hs).isUnit z hz)).mul
    (smooth_extForm h hs hz ξ).conjTranspose).mul ((h.sub hs).mContDiffAt hz).transpose

end Smooth

def Above (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z : V)
    (P : ((Fin 5 → ℂ) → Matrix (m ⊕ l) (m ⊕ l) ℂ) → (Fin 5 → ℂ) → Prop) : Prop :=
  ∀ (L : (Fin 5 → ℂ) →L[ℂ] V) (w : Fin 5 → ℂ), L w = z → P (fun x => H (L x)) w

section Descend

variable {p q : Type*}

variable (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) (hz : z ∈ U)
include h hs hz

end Descend

end GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclicGeneratorsInvariantTop
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

open Polynomial in

theorem GlobalTheory.DetInv.exists_generators_of_charpoly_eq_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (n e N : ℕ) (t T : Matrix (Fin n) (Fin n) k) (h : Polynomial k), 0 < e → h.Monic → h.Separable → t * T = T * t → t ^ e = 0 → (∀ x, t *ᵥ x = 0 → ∃ y, x = t ^ (e - 1) *ᵥ y) → (∀ x, ∃ y, Polynomial.aeval T h *ᵥ x = t *ᵥ y) → T.charpoly = h ^ (e * N) → ∃ x : Fin N → Fin n → k, ∀ U : Submodule k (Fin n → k), (∀ i, x i ∈ U) → (∀ z ∈ U, t *ᵥ z ∈ U) → (∀ z ∈ U, T *ᵥ z ∈ U) → U = ⊤ := by
  intro k _ _ n e N t T h he hmon hsep htT hte hker himg hchar
  obtain ⟨t', ht'⟩ : ∃ t' : Module.End k (Fin n → k), t' = Matrix.toLin' t := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T' : Module.End k (Fin n → k), T' = Matrix.toLin' T := ⟨_, rfl⟩
  have htz : ∀ z, t' z = t *ᵥ z := fun z => by rw [ht', Matrix.toLin'_apply]
  have hTz : ∀ z, T' z = T *ᵥ z := fun z => by rw [hT', Matrix.toLin'_apply]
  have hcz : ∀ z, t' (T' z) = T' (t' z) := fun z => by
    simp only [htz, hTz, Matrix.mulVec_mulVec, htT]
  have hcomm : Commute t' T' := LinearMap.ext fun z => hcz z
  have hpow : ∀ (m : ℕ) z, (t' ^ m) z = t ^ m *ᵥ z := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, ih, htz, Matrix.mulVec_mulVec]
  have hte' : t' ^ e = 0 := LinearMap.ext fun z => by rw [hpow, hte]; simp
  have hker' : ∀ x, t' x = 0 → x ∈ LinearMap.range (t' ^ (e - 1)) := by
    intro x hx
    obtain ⟨y, hy⟩ := hker x (by rw [← htz]; exact hx)
    exact ⟨y, by rw [hpow, hy]⟩
  have hTW : LinearMap.range t' ≤ (LinearMap.range t').comap T' := by
    rintro _ ⟨y, rfl⟩
    exact ⟨T' y, hcz y⟩
  have hc := GlobalTheory.T.charpoly_eq_quotient_charpoly_pow k (Fin n → k) t' T' hcomm e he hte' hker' hTW
  obtain ⟨Tb, hTb⟩ : ∃ Tb : Module.End k ((Fin n → k) ⧸ LinearMap.range t'),
      Tb = (LinearMap.range t').mapQ (LinearMap.range t') T' hTW := ⟨_, rfl⟩
  rw [← hTb] at hc
  have hcT : LinearMap.charpoly T' = T.charpoly := by rw [hT', Matrix.charpoly_toLin']
  have hroot : (LinearMap.charpoly Tb) ^ e = (h ^ N) ^ e := by
    rw [← hc, hcT, hchar, mul_comm, pow_mul]
  have hchb : LinearMap.charpoly Tb = h ^ N :=
    Polynomial.eq_of_monic_of_associated (LinearMap.charpoly_monic Tb) (hmon.pow N)
      (associated_of_dvd_dvd
        ((IsIntegrallyClosed.pow_dvd_pow_iff he.ne').mp hroot.dvd)
        ((IsIntegrallyClosed.pow_dvd_pow_iff he.ne').mp hroot.symm.dvd))
  have hb1 : ∀ x, Tb ((LinearMap.range t').mkQ x) = (LinearMap.range t').mkQ (T' x) := by
    intro x
    rw [hTb]
    rfl
  have hbm : ∀ (m : ℕ) x, (Tb ^ m) ((LinearMap.range t').mkQ x)
      = (LinearMap.range t').mkQ ((T' ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hb1, ih]
  have hmk : ∀ (p : k[X]) x, aeval Tb p ((LinearMap.range t').mkQ x)
      = (LinearMap.range t').mkQ (aeval T' p x) := by
    intro p x
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
    | monomial m c =>
      rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, hbm, map_smul]
  have hA : ∀ x, aeval T' h x = aeval T h *ᵥ x := by
    intro x
    have h1 : T' = Matrix.toLinAlgEquiv' T := hT'
    rw [h1, Polynomial.aeval_algHom_apply]
    exact Matrix.toLin'_apply _ _
  have hTbh : aeval Tb h = 0 := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := (LinearMap.range t').mkQ_surjective v
    rw [hmk, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hA]
    obtain ⟨y, hy⟩ := himg x
    exact ⟨y, by rw [htz, hy]⟩
  obtain ⟨xb, hgen⟩ := GlobalTheory.T.exists_cyclic_generators_separable_min k _ Tb h hmon hsep hTbh N hchb
  choose xs hxs using fun j => (LinearMap.range t').mkQ_surjective (xb j)
  refine ⟨xs, fun U hU htU hTU => ?_⟩
  have hstab : ∀ f : Module.End k (Fin n → k), (∀ z ∈ U, f z ∈ U) →
      ∀ (m : ℕ), ∀ z ∈ U, (f ^ m) z ∈ U := by
    intro f hf m
    induction m with
    | zero => intro z hz; simpa using hz
    | succ m ih =>
      intro z hz
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hf z hz)
  have htm := hstab t' fun z hz => by rw [htz]; exact htU z hz
  have hTm := hstab T' fun z hz => by rw [hTz]; exact hTU z hz
  have hUa : ∀ (p : k[X]), ∀ z ∈ U, aeval T' p z ∈ U := by
    intro p z hz
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, LinearMap.add_apply]
      exact U.add_mem hp hq
    | monomial m c =>
      rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
      exact U.smul_mem c (hTm m z hz)
  have step : ∀ v, ∃ u ∈ U, ∃ w, v = u + t' w := by
    intro v
    obtain ⟨p, hp⟩ := hgen ((LinearMap.range t').mkQ v)
    refine ⟨∑ j, aeval T' (p j) (xs j), U.sum_mem fun j _ => hUa _ _ (hU j), ?_⟩
    have h0 : (LinearMap.range t').mkQ (v - ∑ j, aeval T' (p j) (xs j)) = 0 := by
      rw [map_sub, map_sum, hp, sub_eq_zero]
      exact Finset.sum_congr rfl fun j _ => by rw [← hmk, hxs]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨w, hw⟩ := h0
    exact ⟨w, by rw [hw]; abel⟩
  have iter : ∀ (m : ℕ) v, ∃ u ∈ U, ∃ w, v = u + (t' ^ m) w := by
    intro m
    induction m with
    | zero => intro v; exact ⟨0, U.zero_mem, v, by simp⟩
    | succ m ih =>
      intro v
      obtain ⟨u, hu, w, rfl⟩ := ih v
      obtain ⟨u', hu', w', rfl⟩ := step w
      refine ⟨u + (t' ^ m) u', U.add_mem hu (htm m u' hu'), w', ?_⟩
      rw [map_add, pow_succ, Module.End.mul_apply, add_assoc]
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨u, hu, w, rfl⟩ := iter e v
  rw [hte']
  simpa using hu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegISupMapRankOneLatticeOfGram
section
open NumberField ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory

open scoped ComplexOrder

theorem deg_iSup_map_of_gram : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (hW : HermFam K W) (hV : HermFam K V) (p : ℕ) (M : Fin p → (W →ₗ[K] V)) (ℓ : Submodule (𝓞 K) W)
  (y : Matrix (Fin p) (Fin p) K), ℓ.FG → latRank K ℓ = 1 → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (∀ (s : K →+* ℂ) a b, ∀ c ∈ ℓ, hV.form s (M b c) (M a c) = s (y a b) * hW.form s c c) →
  y.det ≠ 0 ∧ deg hV (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) =
    p * deg hW ℓ - (∑ s : K →+* ℂ, Real.log ‖s y.det‖) / (2 * Module.finrank ℚ K) := by
  intro K _ _ W V _ _ _ _ _ _ _ _ hW hV p M ℓ y hfg hrk hinj hind hgram
  have hr : Module.finrank K (Submodule.span K (ℓ : Set W)) = 1 := hrk
  haveI : FiniteDimensional K (Submodule.span K (ℓ : Set W)) :=
    Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  obtain ⟨c, hcℓ, hc0⟩ : ∃ c ∈ ℓ, c ≠ 0 := by
    by_contra hne
    push_neg at hne
    have h0 : Submodule.span K (ℓ : Set W) = ⊥ := by
      rw [Submodule.span_eq_bot]; intro x hx; exact hne x hx
    rw [h0, finrank_bot] at hr; exact zero_ne_one hr
  have hspan : (ℓ : Set W) ⊆ Submodule.span K {c} := by
    have hle : Submodule.span K {c} ≤ Submodule.span K (ℓ : Set W) :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr hcℓ)
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hr, finrank_span_singleton hc0])
    rw [heq]; exact Submodule.subset_span
  have hfℓ : IsFrame K ℓ ![c] := by
    refine ⟨fun i => by fin_cases i; simpa using hcℓ, ?_, ?_⟩
    · exact linearIndependent_unique_iff.mpr (by simpa using hc0)
    · intro x hx
      refine Submodule.span_mono ?_ (hspan hx)
      rintro _ rfl; exact ⟨0, rfl⟩
  set v : Fin p → V := fun a => M a c with hvdef
  have hvS : ∀ a, v a ∈ ℓ.map ((M a).restrictScalars (𝓞 K)) := fun a => ⟨c, hcℓ, rfl⟩
  have hfS : IsFrame K (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) v := by
    refine ⟨fun a => (le_iSup (fun a => ℓ.map ((M a).restrictScalars (𝓞 K))) a) (hvS a), ?_, ?_⟩
    · exact iSupIndep.linearIndependent _ hind (fun a => Submodule.subset_span (hvS a))
        (fun a h => hc0 (hinj a (h.trans (map_zero (M a)).symm)))
    · intro x hx
      have hle : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) ≤
          (Submodule.span K (Set.range v)).restrictScalars (𝓞 K) := by
        refine iSup_le fun a => ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp (hspan hz)
        rw [Submodule.restrictScalars_mem, LinearMap.restrictScalars_apply, LinearMap.map_smul]
        exact Submodule.smul_mem _ k (Submodule.subset_span ⟨a, rfl⟩)
      exact hle hx
  have hSfg : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).FG :=
    Submodule.fg_iSup _ (fun a => hfg.map _)
  have hidx : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
      ((Submodule.span (𝓞 K) {c}).toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
    have h1 : Submodule.span (𝓞 K) (Set.range v) =
        ⨆ a, (Submodule.span (𝓞 K) {c}).map ((M a).restrictScalars (𝓞 K)) := by
      rw [Submodule.span_range_eq_iSup]
      congr 1; funext a
      rw [Submodule.map_span, Set.image_singleton]; rfl
    rw [h1]
    exact GlobalTheory.T.relIndex_iSup_map_eq_relIndex_pow K W V p M ℓ _ ((Submodule.span_singleton_le_iff_mem _ _).mpr hcℓ) hinj hind
  have hgr : ∀ s : K →+* ℂ, hV.gram s v = hW.form s c c • (s.mapMatrix y).transpose := by
    intro s; ext i j
    simp [HermFam.gram, v, hgram s j i c hcℓ, mul_comm]
  have hdet : ∀ s : K →+* ℂ, (hV.gram s v).det = (hW.form s c c) ^ p * s y.det := by
    intro s; rw [hgr, Matrix.det_smul, Matrix.det_transpose, RingHom.map_det, Fintype.card_fin]
  have hpos : ∀ s : K →+* ℂ, 0 < (hV.gram s v).det := fun s => (hV.posDef s p v hfS.2.1).det_pos
  have hA1 : ∀ s : K →+* ℂ, 0 < hW.form s c c := fun s => by
    have := (hW.posDef s 1 ![c] hfℓ.2.1).det_pos
    simpa [Matrix.det_fin_one] using this
  have hAeq : ∀ s : K →+* ℂ, hW.form s c c = (((hW.form s c c).re : ℝ) : ℂ) := fun s =>
    Complex.ext (by simp) (by simp [← (Complex.pos_iff.mp (hA1 s)).2])
  have hkey : ∀ s : K →+* ℂ, 0 < (s y.det).re ∧ (s y.det).im = 0 ∧
      (hV.gram s v).det.re = (hW.form s c c).re ^ p * (s y.det).re := by
    intro s
    have h1 := Complex.pos_iff.mp (hpos s)
    have hA := (Complex.pos_iff.mp (hA1 s)).1
    rw [hdet s, hAeq s, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.im_ofReal_mul] at h1
    have hApow : 0 < (hW.form s c c).re ^ p := pow_pos hA p
    refine ⟨pos_of_mul_pos_right h1.1 hApow.le, ?_, ?_⟩
    · exact (mul_eq_zero.mp h1.2.symm).resolve_left hApow.ne'
    · rw [hdet s, hAeq s, ← Complex.ofReal_pow, Complex.re_ofReal_mul]; simp
  have hlogV : ∀ s : K →+* ℂ, Real.log (hV.gram s v).det.re =
      p * Real.log (hW.form s c c).re + Real.log ‖s y.det‖ := by
    intro s
    obtain ⟨hre, him, heq⟩ := hkey s
    have hn : ‖s y.det‖ = (s y.det).re := by
      rw [← Complex.abs_re_eq_norm.mpr him, abs_of_pos hre]
    rw [heq, hn, Real.log_mul (pow_pos (Complex.pos_iff.mp (hA1 s)).1 p).ne' hre.ne', Real.log_pow]
  have hlogW : ∀ s : K →+* ℂ, Real.log (hW.gram s ![c]).det.re = Real.log (hW.form s c c).re := by
    intro s; simp [HermFam.gram, Matrix.det_fin_one]
  refine ⟨?_, ?_⟩
  · obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
    intro h; have := (hkey s).1; rw [h, map_zero] at this; simp at this
  · rw [arakelovDegree_eq_degreeOfFamily hV hSfg hfS, arakelovDegree_eq_degreeOfFamily hW hfg hfℓ]
    unfold degreeOfFamily
    have hrg : Set.range ![c] = {c} := by ext x; simp [eq_comm]
    rw [hrg, hidx, Nat.cast_pow, Real.log_pow, Finset.sum_congr rfl (fun s _ => hlogV s),
      Finset.sum_congr rfl (fun s _ => hlogW s), Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTopPartEqZero
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem delta_topPart_eq_zero {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E)
    (c : Finset ι → E) (k : ℕ) (hc : Dtot d c = 0) (hk : ∀ s, k < s.card → c s = 0) :
    delta (fun s => if s.card = k then c s else 0) = 0 := by
  funext t
  by_cases ht : t.card = k + 1
  · have h1 : delta c t = 0 := by
      have h := congrFun hc t
      simpa [Dtot, hk t (by omega)] using h
    rw [Pi.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : (t.erase i).card = k := by rw [Finset.card_erase_of_mem hi]; omega
    simp only [this, if_true]
  · refine Finset.sum_eq_zero fun i hi => ?_
    have h0 := Finset.card_erase_add_one hi
    have : (t.erase i).card ≠ k := by omega
    simp only [this, if_false, smul_zero]

theorem hypZero_of_cechZero : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → ∀ n, (∀ q b, q + b = n → CechZero (T q) b) → HypZero d T n := by
  intro ι _ E _ d T hdd hmono hdT n hC
  obtain ⟨-, -, hadd, hsub, -, hDD⟩ := GlobalTheory.T.cech_and_total_differential_additive_square_zero (ι := ι) d
  have key : ∀ k, k ≤ n + 1 → ∀ c, InTot T (n + 1) c → Dtot d c = 0 →
      (∀ s, k < s.card → c s = 0) → ∃ y, InTot T n y ∧ Dtot d y = c := by
    intro k
    induction k with
    | zero =>
      intro _ c hc _ h0
      refine ⟨0, ⟨rfl, fun q s _ => (T q s).zero_mem, fun _ _ => rfl⟩, ?_⟩
      funext s
      have hs : c s = 0 := by
        rcases Nat.eq_zero_or_pos s.card with h | h
        · rw [Finset.card_eq_zero.1 h]; exact hc.1
        · exact h0 s h
      simp [Dtot, delta, hs]
    | succ b ih =>
      intro hb c hc hD h0
      obtain ⟨q, hq⟩ : ∃ q, q + b = n := ⟨n - b, by omega⟩
      have hin : InCech (T q) (b + 1) (fun s => if s.card = b + 1 then c s else 0) := by
        refine ⟨by simp, fun s => ?_, fun s hs => by simp [hs]⟩
        by_cases hs : s.card = b + 1
        · simp only [hs, if_true]
          exact hc.2.1 q s (by omega)
        · simp only [hs, if_false]
          exact (T q s).zero_mem
      obtain ⟨y, hy, hyc⟩ := hC q b hq _ hin (delta_topPart_eq_zero d c (b + 1) hD h0)
      have hyT : InTot T n y := by
        refine ⟨hy.1, fun q' s hs => ?_, fun s hs => hy.2.2 s (by omega)⟩
        by_cases h : s.card = b
        · obtain rfl : q' = q := by omega
          exact hy.2.1 s
        · rw [hy.2.2 s h]; exact (T q' s).zero_mem
      have hDy : InTot T (n + 1) (Dtot d y) := (GlobalTheory.T.isTotalCochainOfDegree_succ_of_differentials d T hmono n y hyT).2 hdT
      have h1 : InTot T (n + 1) (c - Dtot d y) := by
        refine ⟨?_, fun q' s hs => (T q' s).sub_mem (hc.2.1 q' s hs) (hDy.2.1 q' s hs),
          fun s hs => ?_⟩
        · rw [Pi.sub_apply, hc.1, hDy.1, sub_zero]
        · rw [Pi.sub_apply, hc.2.2 s hs, hDy.2.2 s hs, sub_zero]
      have h2 : Dtot d (c - Dtot d y) = 0 := by rw [hsub, hD, hDD hdd, sub_zero]
      have h3 : ∀ s, b < s.card → (c - Dtot d y) s = 0 := by
        intro s hs
        have hys : y s = 0 := hy.2.2 s (by omega)
        by_cases h : s.card = b + 1
        · simp [Dtot, hyc, hys, h]
        · simp [Dtot, hyc, hys, h, h0 s (by omega)]
      obtain ⟨z, hz, hzc⟩ := ih (by omega) _ h1 h2 h3
      refine ⟨z + y, ⟨?_, fun q' s hs => (T q' s).add_mem (hz.2.1 q' s hs) (hyT.2.1 q' s hs),
        fun s hs => ?_⟩, ?_⟩
      · rw [Pi.add_apply, hz.1, hyT.1, add_zero]
      · rw [Pi.add_apply, hz.2.2 s hs, hyT.2.2 s hs, add_zero]
      · rw [hadd, hzc, sub_add_cancel]
  intro c hc hD
  exact key (n + 1) le_rfl c hc hD hc.2.2

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorDescentFlatNormalDomainsStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_descent_flat_normal_domains : ∀ (A' B' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A' B']
    [Module.Flat A' B'] (s : A'), s ≠ 0 →
    (∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → s ∈ 𝔭 → (𝔭.map (algebraMap A' B')).IsPrime) →
    ∀ b c : B', b * c = algebraMap A' B' s →
    b ∈ ((Ideal.span {b}).comap (algebraMap A' B')).map (algebraMap A' B') := by
  first | (exact @GlobalTheory.DivDescent.divisor_descent) | (exact GlobalTheory.DivDescent.divisor_descent) | (intros; apply GlobalTheory.DivDescent.divisor_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsAllPrimesOfClosedFibreStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorsOfConstantsAllPrimes_of_closedFibre : GlobalTheory.VertUnits.DivConstLocal → GlobalTheory.VertUnits.DivConstAll := by
  first | exact @GlobalTheory.VertUnits.divConstAll_of_divConstLocal | exact GlobalTheory.VertUnits.divConstAll_of_divConstLocal | (intros; apply GlobalTheory.VertUnits.divConstAll_of_divConstLocal <;> assumption)
end

