import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankPeriodFunctorCoeffBaseChange
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CoeffBC

section General

variable {L L' : Type} [Field L] [Field L'] [Algebra L L'] {ι : Type} [Fintype ι] [DecidableEq ι]
  {M M' : Type} [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L' M'] [Module L M']
  {N N' : Type} [AddCommGroup N] [Module L N] [AddCommGroup N'] [Module L' N'] [Module L N']

def IsCoord (u : ι → L') (J : M →ₗ[L] M') (π : ι → M' →ₗ[L] M) : Prop :=
  (∀ x, ∑ k, u k • J (π k x) = x) ∧ ∀ k l m, π k (u l • J m) = if k = l then m else 0

def Rel (π : ι → M' →ₗ[L] M) (S : Submodule L M) (S' : Submodule L' M') : Prop :=
  ∀ x, x ∈ S' ↔ ∀ k, π k x ∈ S

theorem exists_isCoord [IsScalarTower L L' M'] (u : Basis ι L L') (J : M →ₗ[L] M')
    (h : IsBaseChange L' J) : ∃ π : ι → M' →ₗ[L] M, IsCoord u J π := by
  let π : ι → M' →ₗ[L] M := fun k =>
    (TensorProduct.lid L M).toLinearMap ∘ₗ LinearMap.rTensor M (u.coord k) ∘ₗ
      (h.equiv.symm.toLinearMap.restrictScalars L)
  have hπ : ∀ k (s : L') (m : M), π k (s • J m) = u.repr s k • m := by
    intro k s m
    have : h.equiv.symm (s • J m) = s ⊗ₜ[L] m := by
      rw [LinearEquiv.symm_apply_eq, h.equiv_tmul]
    simp only [π, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, this]
    simp
  refine ⟨π, fun x => ?_, fun k l m => ?_⟩
  · obtain ⟨y, rfl⟩ := h.equiv.surjective x
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      rw [h.equiv_tmul]
      simp only [hπ, map_smul]
      conv_rhs => rw [← u.sum_repr s, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_assoc, smul_comm]
    | add a b ha hb =>
      simp only [map_add, smul_add, Finset.sum_add_distrib, ha, hb]
  · rw [hπ, u.repr_self, Finsupp.single_apply]
    by_cases hk : k = l
    · simp [hk]
    · simp [hk, Ne.symm hk]

variable {u : ι → L'} {J : M →ₗ[L] M'} {π : ι → M' →ₗ[L] M}
  {JN : N →ₗ[L] N'} {πN : ι → N' →ₗ[L] N}

theorem IsCoord.sum (h : IsCoord u J π) (m : ι → M) (k : ι) :
    π k (∑ l, u l • J (m l)) = m k := by
  simp [map_sum, h.2]

theorem IsCoord.comm (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) (k : ι) (x : N') :
    π k (f' x) = f (πN k x) := by
  conv_lhs => rw [← hN.1 x]
  simp only [map_sum f', map_smul, hf]
  exact h.sum _ k

theorem IsCoord.rel_ker (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) :
    Rel πN (LinearMap.ker f) (LinearMap.ker f') := by
  intro x
  simp only [LinearMap.mem_ker, ← h.comm hN f f' hf]
  refine ⟨fun hx k => by simp [hx], fun hx => ?_⟩
  rw [← h.1 (f' x)]
  simp [hx]

theorem IsCoord.rel_range (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) :
    Rel π (LinearMap.range f) (LinearMap.range f') := by
  intro x
  constructor
  · rintro ⟨y, rfl⟩ k
    exact ⟨_, (h.comm hN f f' hf k y).symm⟩
  · intro hx
    choose y hy using hx
    refine ⟨∑ k, u k • JN (y k), ?_⟩
    simp only [map_sum, map_smul, hf, hy]
    exact h.1 x

omit [Algebra L L'] [Fintype ι] [DecidableEq ι] in
theorem Rel.inf {S T : Submodule L M} {S' T' : Submodule L' M'} (h : Rel π S S')
    (h' : Rel π T T') : Rel π (S ⊓ T) (S' ⊓ T') := by
  intro x
  simp only [Submodule.mem_inf, h x, h' x, forall_and]

omit [Algebra L L'] [Fintype ι] [DecidableEq ι] in
theorem Rel.iInf {κ : Type} {S : κ → Submodule L M} {S' : κ → Submodule L' M'}
    (h : ∀ i, Rel π (S i) (S' i)) : Rel π (⨅ i, S i) (⨅ i, S' i) := by
  intro x
  simp only [Submodule.mem_iInf, fun i => h i x]
  exact forall_comm

theorem IsCoord.nonempty_equiv [IsScalarTower L L' M'] (h : IsCoord u J π) {S : Submodule L M}
    {S' : Submodule L' M'} (hS : Rel π S S') : Nonempty (S' ≃ₗ[L] (ι → S)) := by
  let F : S' →ₗ[L] (ι → S) := LinearMap.pi fun k =>
    LinearMap.codRestrict S (π k ∘ₗ (S'.subtype.restrictScalars L))
      (fun x => (hS x.1).1 x.2 k)
  have hF : ∀ x k, (F x k : M) = π k x := fun _ _ => rfl
  refine ⟨LinearEquiv.ofBijective F ⟨?_, ?_⟩⟩
  · intro x y hxy
    apply Subtype.ext
    rw [← h.1 x, ← h.1 y]
    simp only [← hF, hxy]
  · intro m
    refine ⟨⟨∑ l, u l • J (m l), (hS _).2 fun k => ?_⟩, ?_⟩
    · rw [h.sum (fun l => (m l : M))]; exact (m k).2
    · funext k
      apply Subtype.ext
      rw [hF]
      exact h.sum (fun l => (m l : M)) k

theorem IsCoord.finrank_eq [IsScalarTower L L' M'] {u : Basis ι L L'} (h : IsCoord u J π)
    {S : Submodule L M} {S' : Submodule L' M'} (hS : Rel π S S') :
    finrank L' S' = finrank L S := by
  obtain ⟨e⟩ := h.nonempty_equiv hS
  haveI : Module.Finite L L' := Module.Finite.of_basis u
  have h1 : finrank L L' * finrank L' S' = finrank L S' := Module.finrank_mul_finrank L L' S'
  have h2 : finrank L (ι → S) = Fintype.card ι * finrank L S := by
    simp [Module.finrank, rank_fun_eq_lift_mul]
  rw [e.finrank_eq, h2, ← Module.finrank_eq_card_basis u] at h1
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

theorem IsCoord.finite_iff [IsScalarTower L L' M'] {u : Basis ι L L'} (h : IsCoord u J π)
    {S : Submodule L M} {S' : Submodule L' M'} (hS : Rel π S S') :
    Module.Finite L' S' ↔ Module.Finite L S := by
  obtain ⟨e⟩ := h.nonempty_equiv hS
  haveI : Module.Finite L L' := Module.Finite.of_basis u
  obtain ⟨k⟩ := u.index_nonempty
  constructor
  · intro _
    haveI : Module.Finite L S' := Module.Finite.trans L' S'
    haveI : Module.Finite L (ι → S) := Module.Finite.equiv e
    exact Module.Finite.of_surjective (LinearMap.proj k : (ι → S) →ₗ[L] S)
      (LinearMap.proj_surjective k)
  · intro _
    haveI : Module.Finite L S' := Module.Finite.equiv e.symm
    exact Module.Finite.of_restrictScalars_finite L L' S'

theorem IsCoord.tensor {Q : Type} [Field Q] [Algebra Q L] [Algebra Q L'] [Module Q M] [Module Q M']
    [IsScalarTower Q L M] [IsScalarTower Q L M'] [IsScalarTower Q L' M']
    (h : IsCoord u J π) (C : Type) [AddCommGroup C] [Module Q C] :
    IsCoord u (AlgebraTensorModule.map J (LinearMap.id : C →ₗ[Q] C))
      (fun k => AlgebraTensorModule.map (π k) (LinearMap.id : C →ₗ[Q] C)) := by
  constructor
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, h.1]
    | add a b ha hb => simp only [map_add, smul_add, Finset.sum_add_distrib, ha, hb]
  · intro k l x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, TensorProduct.smul_tmul', h.2]
      split_ifs <;> simp
    | add a b ha hb =>
      simp only [map_add, smul_add, ha, hb]
      split_ifs <;> simp

theorem map_comm {Q : Type} [Field Q] [Algebra Q L] [Algebra Q L'] [Module Q M] [Module Q M']
    [IsScalarTower Q L M] [IsScalarTower Q L M'] [IsScalarTower Q L' M']
    {C D : Type} [AddCommGroup C] [Module Q C] [AddCommGroup D] [Module Q D]
    (f : M →ₗ[L] M) (f' : M' →ₗ[L'] M') (hf : ∀ m, f' (J m) = J (f m)) (φ : C →ₗ[Q] D)
    (y : M ⊗[Q] C) :
    AlgebraTensorModule.map f' φ (AlgebraTensorModule.map J (LinearMap.id : C →ₗ[Q] C) y) =
      AlgebraTensorModule.map J (LinearMap.id : D →ₗ[Q] D) (AlgebraTensorModule.map f φ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m c => simp [hf]
  | add a b ha hb => simp only [map_add, ha, hb]

end General

theorem finrank_baseChange : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) (LL LL' : Type) [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL'] [FiniteDimensional LL LL'] (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL' V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V'] (ρ : Representation LL G V) (ρ' : Representation LL' G V') (j : V →ₗ[LL] V'), IsBaseChange LL' j → (∀ g x, j (ρ g x) = ρ' g (j x)) → finrank LL' V' = finrank LL V ∧ finrank LL' ↥(H0V ρ') = finrank LL ↥(H0V ρ) ∧ (finrank LL' ↥(Dcris PD ρ') = finrank LL ↥(Dcris PD ρ) ∧ (Module.Finite LL' ↥(Dcris PD ρ') ↔ Module.Finite LL ↥(Dcris PD ρ))) ∧ (finrank LL' ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) ∧ (Module.Finite LL' ↥(DdR PD ρ') ↔ Module.Finite LL ↥(DdR PD ρ))) ∧ (∀ a : ℤ, finrank LL' ↥(DdR PD ρ' ⊓ FilV PD (LL := LL') (V := V') a) = finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)) ∧ (∀ τ : K₀ →ₐ[Qp] LL, finrank LL' ↥(DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DcrisL PD ρ τ)) ∧ ∀ τ : K →ₐ[Qp] LL, finrank LL' ↥(DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, finrank LL' ↥(FildR PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a) = finrank LL ↥(FildR PD ρ τ a) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL LL' _ _ _ _ _ _ _ V V' _ _ _ _ _ _ _ _ _ _ ρ ρ' j hj hρ
  classical
  haveI : IsScalarTower Qp LL V' := IsScalarTower.of_algebraMap_smul fun r x => by
    rw [← algebraMap_smul LL' (algebraMap Qp LL r) x, ← IsScalarTower.algebraMap_apply,
      algebraMap_smul]
  let u := Module.finBasis LL LL'
  obtain ⟨π, h⟩ := exists_isCoord u j hj
  have hB := h.tensor (Q := Qp) B
  have hR := h.tensor (Q := Qp) BdR
  have r0 : Rel π (H0V ρ) (H0V ρ') :=
    Rel.iInf fun g => h.rel_ker h _ _ fun y => by simp [hρ]
  have rc : Rel _ (Dcris PD ρ) (Dcris PD ρ') :=
    Rel.iInf fun g => hB.rel_ker hB _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, actVB]
      rw [map_comm (ρ g) (ρ' g) (fun m => (hρ g m).symm)]
  have rd : Rel _ (DdR PD ρ) (DdR PD ρ') :=
    Rel.iInf fun g => hR.rel_ker hR _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, actVdR]
      rw [map_comm (ρ g) (ρ' g) (fun m => (hρ g m).symm)]
  have rf : ∀ a : ℤ,
      Rel (fun k => AlgebraTensorModule.map (π k) (LinearMap.id : BdR →ₗ[Qp] BdR))
        (FilV PD (LL := LL) (V := V) a) (FilV PD (LL := LL') (V := V') a) := by
    intro a
    have hF := h.tensor (Q := Qp) ↥((PD.Fil a).restrictScalars Qp)
    refine hR.rel_range hF
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype)
      (AlgebraTensorModule.map (LinearMap.id : V' →ₗ[LL'] V')
        ((PD.Fil a).restrictScalars Qp).subtype) fun y => ?_
    exact map_comm (J := j) LinearMap.id LinearMap.id (fun _ => rfl)
      ((PD.Fil a).restrictScalars Qp).subtype y
  have re : ∀ τ : K →ₐ[Qp] LL,
      Rel _ (DdRE PD ρ τ) (DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) :=
    fun τ => rd.inf (Rel.iInf fun c => hR.rel_ker hR _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, mulVdR,
        map_smul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rw [map_comm (L' := LL') (J := j) LinearMap.id LinearMap.id (fun _ => rfl)])
  have rl : ∀ τ : K₀ →ₐ[Qp] LL,
      Rel _ (DcrisL PD ρ τ) (DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) :=
    fun τ => rc.inf (Rel.iInf fun c => hB.rel_ker hB _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, mulVB,
        map_smul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rw [map_comm (L' := LL') (J := j) LinearMap.id LinearMap.id (fun _ => rfl)])
  refine ⟨?_, h.finrank_eq r0, ⟨hB.finrank_eq rc, hB.finite_iff rc⟩,
    ⟨hR.finrank_eq rd, hR.finite_iff rd⟩, fun a => hR.finrank_eq (rd.inf (rf a)),
    fun τ => hB.finrank_eq (rl τ),
    fun τ => ⟨hR.finrank_eq (re τ), fun a => hR.finrank_eq ((re τ).inf (rf a))⟩⟩
  have := h.finrank_eq (S := ⊤) (S' := ⊤) (fun x => by simp)
  simpa using this

end GlobalTheory.CoeffBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionSubMemSpanPowSucc
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

namespace GlobalTheory.GamFilt

theorem sub_mem_pow_succ {A : Type*} [CommRing A] (f : A →+* A) (I : Ideal A)
    (h0 : ∀ a, f a - a ∈ I) (h1 : ∀ a ∈ I, f a - a ∈ I ^ 2) :
    ∀ k : ℕ, ∀ a ∈ I ^ k, f a - a ∈ I ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro a _; simpa using h0 a
  | succ k ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      have hfy : f y ∈ I := by
        have := I.add_mem (h0 y) hy
        simpa using this
      have e : f (x * y) - x * y = (f x - x) * f y + x * (f y - y) := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (ih x hx) hfy
      · rw [show k + 1 + 1 = k + 2 from rfl, pow_add]
        exact Ideal.mul_mem_mul hx (h1 y hy)
    · intro x y hx hy
      have e : f (x + y) - (x + y) = (f x - x) + (f y - y) := by
        rw [map_add]; ring
      rw [e]
      exact Ideal.add_mem _ hx hy

theorem sub_mem_pow_succ_pair {A : Type*} [CommRing A] (f : A →+* A) (p t : A)
    (h0 : ∀ a, f a - a ∈ Ideal.span {p, t}) (hp : f p = p)
    (ht : f t - t ∈ Ideal.span {p, t} ^ 2) :
    ∀ k : ℕ, ∀ a ∈ Ideal.span {p, t} ^ k, f a - a ∈ Ideal.span {p, t} ^ (k + 1) := by
  refine sub_mem_pow_succ f _ h0 ?_
  intro y hy
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hy
  have e : f (a * p + b * t) - (a * p + b * t) =
      (f a - a) * p + (f b - b) * t + f b * (f t - t) := by
    rw [map_add, map_mul, map_mul, hp]; ring
  rw [e]
  have hpm : p ∈ Ideal.span {p, t} := Ideal.subset_span (by simp)
  have htm : t ∈ Ideal.span {p, t} := Ideal.subset_span (by simp)
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) (Ideal.mul_mem_left _ _ ht)
  · rw [pow_two]; exact Ideal.mul_mem_mul (h0 a) hpm
  · rw [pow_two]; exact Ideal.mul_mem_mul (h0 b) htm

theorem X_dvd_sub {O : Type*} [CommRing O] (g : PowerSeries O →ₐ[O] PowerSeries O)
    (hg : PowerSeries.constantCoeff (g PowerSeries.X) = 0) (a : PowerSeries O) :
    PowerSeries.X ∣ g a - a := by
  have h1 : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]; simp
  obtain ⟨b, hb⟩ := h1
  have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
    rw [← hb, PowerSeries.algebraMap_apply]; simp
  rw [PowerSeries.X_dvd_iff, ha, map_add, AlgHom.commutes, map_mul]
  simp [hg]

theorem exists_X_sub {O : Type*} [CommRing O] (F : PowerSeries O) (p : ℕ) (c : O)
    (h0 : PowerSeries.constantCoeff F = 0) (h1 : PowerSeries.coeff 1 F = 1 + p * c) :
    ∃ h : PowerSeries O, F - PowerSeries.X =
      PowerSeries.X * ((p : PowerSeries O) * PowerSeries.C c + PowerSeries.X * h) := by
  have : PowerSeries.X ^ 2 ∣ F - PowerSeries.X - PowerSeries.X * (PowerSeries.C ((p : O) * c)) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [h0]
    · rw [map_sub, map_sub, h1, PowerSeries.coeff_succ_X_mul]
      simp
  obtain ⟨h, hh⟩ := this
  refine ⟨h, ?_⟩
  rw [map_mul, map_natCast] at hh
  linear_combination hh

theorem letγ_sub_mem {O : Type} [CommRing O] {n : ℕ} (g : PowerSeries O →ₐ[O] PowerSeries O) (p : ℕ)
    (c : O) (h0 : PowerSeries.constantCoeff (g PowerSeries.X) = 0)
    (h1 : PowerSeries.coeff 1 (g PowerSeries.X) = 1 + p * c) :
    ∀ k : ℕ, ∀ a ∈ (Ideal.span {((p : ℕ) : LetA O n), letπ}) ^ k,
      letγ g a - a ∈ (Ideal.span {((p : ℕ) : LetA O n), letπ}) ^ (k + 1) := by
  have hpm : ((p : ℕ) : LetA O n) ∈ Ideal.span {((p : ℕ) : LetA O n), letπ} :=
    Ideal.subset_span (by simp)
  have htm : (letπ : LetA O n) ∈ Ideal.span {((p : ℕ) : LetA O n), letπ} :=
    Ideal.subset_span (by simp)
  refine sub_mem_pow_succ_pair (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom _ _ ?_ (map_natCast _ _) ?_
  · intro a
    choose b hb using fun i => X_dvd_sub g h0 (a i)
    have e : (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom a - a = letπ * b := funext hb
    rw [e]
    exact Ideal.mul_mem_right _ _ htm
  · obtain ⟨h, hh⟩ := exists_X_sub _ p c h0 h1
    have e : (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom letπ - letπ =
        letπ * (((p : ℕ) : LetA O n) * (fun _ => PowerSeries.C c) + letπ * (fun _ => h)) :=
      funext fun _ => hh
    rw [e, pow_two]
    exact Ideal.mul_mem_mul htm (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hpm)
      (Ideal.mul_mem_right _ _ htm))

theorem exists_eq_one_add {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (u : ↥(OL LL))
    (hu : (1 : WithTop ℚ) ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 u - 1)) :
    ∃ c : ↥(OL LL), u = 1 + (l : ↥(OL LL)) * c := by
  have hl : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set y : ↥LL.1 := (algebraMap ↥(OL LL) ↥LL.1 u - 1) / (l : ↥LL.1) with hy
  have e : algebraMap ↥(OL LL) ↥LL.1 u - 1 = (l : ↥LL.1) * y := by
    rw [hy]; field_simp
  rw [e, AddValuation.map_mul, P.v_l] at hu
  have h0 : 0 ≤ P.v LL y := by
    have : (1 : WithTop ℚ) + 0 ≤ 1 + P.v LL y := by simpa using hu
    exact (WithTop.add_le_add_iff_left WithTop.one_ne_top).1 this
  refine ⟨⟨y, (P.v_O LL y).1 h0⟩, Subtype.ext ?_⟩
  have : (u : ↥LL.1) - 1 = (l : ↥LL.1) * y := e
  push_cast
  linear_combination this

theorem gamma_sub_mem_pow_succ : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ g ∈ W.GKs, ∀ (k : ℕ), ∀ a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ k, W.γA (W.resΓ g) a - a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ (k + 1) := by
  intro D HW l _ K s LL h W g hg
  have h1 := (W.GKs_def g).1 hg
  rw [← W.χΓ_res g] at h1
  have hs : (1 : WithTop ℚ) ≤ (W.s : WithTop ℚ) := by exact_mod_cast W.s_pos
  obtain ⟨c, hc⟩ := exists_eq_one_add (D.loc l) LL _ (hs.trans h1)
  exact letγ_sub_mem (W.γ₀ (W.resΓ g)) l c (W.γ₀_X _).1 ((W.γ₀_X _).2.trans hc)

end GlobalTheory.GamFilt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisMore
section
namespace GlobalTheory.NonzeroScalarLattice

theorem exists_ne_zero_smul_mem {G : Type} [Group G] {LL : Type} [Field LL] {O : Type}
    [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [IsDomain O] [IsFractionRing O LL]
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (w : V) :
    ∃ (b : O), b ≠ (0 : O) ∧ b • w ∈ Formalism.WeaklyAdmissibleFiltrations.Lattice.T L := by
  have hw : w ∈ Submodule.span LL (L.T : Set V) := by
    rw [L.span]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.T.smul_mem _ hax
    · rw [mul_smul]; exact L.T.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := O) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap O LL q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective O LL (by rw [h, map_zero]))
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h1 : q • ((algebraMap O LL p / algebraMap O LL q) • x) = p • x := by
      rw [← algebraMap_smul LL q, smul_smul, mul_div_cancel₀ _ hq1, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.T.smul_mem _ hax

end GlobalTheory.NonzeroScalarLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocAinfUntiltEpsOneEqZeta
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.TiedMu

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem zeta_pow (AI : LocAinf l P) (k n : ℕ) : AI.ζ (n + k) ^ l ^ n = AI.ζ k := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, Nat.add_right_comm, AI.ζ_succ, ih]

theorem untilt_eps (AI : LocAinf l P) : AI.ε.untilt = 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩
  have h := zeta_pow AI 0 n
  rw [add_zero, AI.ζ_zero] at h
  rw [h]

theorem locAinf_untilt_epsOne_eq_zeta (AI : LocAinf l P) : AI.ε1.untilt = AI.ζ 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ (n + 1), ?_, ?_⟩
  · refine (AI.ε_coeff (n + 1)).symm.trans ?_
    have h : AI.ε = AI.ε1 ^ l := by rw [LocAinf.ε1, frobeniusEquiv_symm_pow_p]
    rw [h]
    exact Perfection.coeff_pow_p _ _
  · rw [zeta_pow AI 1 n]

theorem eps_ne_one (AI : LocAinf l P) : AI.ε ≠ 1 := by
  intro h
  apply AI.ζ_one
  rw [← locAinf_untilt_epsOne_eq_zeta, LocAinf.ε1, h, map_one, map_one]

theorem eps_pow_ne_one (AI : LocAinf l P) (j : ℕ) : AI.ε ^ l ^ j ≠ 1 := by
  induction j with
  | zero => simpa using eps_ne_one AI
  | succ j ih =>
    intro h
    apply ih
    apply (frobeniusEquiv (OCb l) l).injective
    rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, ← pow_mul,
      ← pow_succ, h, one_pow]

theorem eps_root_pow (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]
    exact ih

theorem isUnit_aB (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (Per.aB l (Per.tm e - 1)) :=
  GlobalTheory.CrisLoc.unit_of_root_aB l e he hne

theorem isUnit_of_aB {AI : LocAinf l P} (T : LocTied l P AI) (a : Ainf l) (h : IsUnit (Per.aB l a)) :
    IsUnit (AI.ιA a) := by
  rw [← T.ιA] at h
  have h' := h.map T.eB.symm
  rwa [RingEquiv.symm_apply_apply] at h'

theorem tied_mu_units : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ s : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) ∧ (∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1))) ∧ IsUnit (AI.ιA AI.ξ) ∧ ∀ z : ℤ_[l], AI.ιA (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
  intro l _ P AI T
  have hj : ∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1)) := fun j =>
    isUnit_of_aB T _ (isUnit_aB (AI.ε ^ l ^ j)
      (by rw [map_pow, untilt_eps, one_pow]) (eps_pow_ne_one AI j))
  have hμ : IsUnit (AI.ιA AI.μ) := by simpa [LocAinf.μ] using hj 0
  refine ⟨fun s => ?_, hj, ?_, fun z => ?_⟩
  · have h := geom_sum_mul (WittVector.teichmuller l (AI.εroot s)) (l ^ s)
    rw [← map_pow, eps_root_pow] at h
    rw [LocAinf.μ, ← h, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · rw [AI.μ_eq, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · apply T.eB.injective
    rw [T.ιA, T.zB]
    exact GlobalTheory.RingIface.aB_algebraMap_padicInt l z

end GlobalTheory.TiedMu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiInjectiveQuotientH2Statement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_injective_quotient_H2 : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G], PadicCoeff p O → ∀ {ε : G →* Oˣ}, Continuous (fun g : G => ((ε g : Oˣ) : O)) → ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ, Function.Injective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  first | exact @GlobalTheory.NatQuot.phi_quot_pow_injective | exact GlobalTheory.NatQuot.phi_quot_pow_injective | (intros; apply GlobalTheory.NatQuot.phi_quot_pow_injective <;> assumption)
end

