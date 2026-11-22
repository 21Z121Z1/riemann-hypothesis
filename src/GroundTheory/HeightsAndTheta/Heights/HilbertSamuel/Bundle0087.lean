import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0069
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0081
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenSESStep

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem isMultiHomog_mul {p q : MRingOver S ι} {a b : K → ℕ} (hp : IsMultiHomog p a)
    (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hp m₁ h₁ k, hq m₂ h₂ k]

theorem isMultiHomog_X (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver S ι) (fun l => if l = k then 1 else 0) := by
  classical
  intro m hm l
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
  by_cases hl : l = k
  · subst hl
    simp [Finsupp.single_apply]
  · have : ∀ j : ι l, (Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1) ⟨l, j⟩ = 0 := by
      intro j
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hl (congrArg Sigma.fst h).symm
    simp [this, hl]

theorem cellMon_homog {I : ∀ k, Finset (ι k)} {u : MRingOver S ι} (hu : u ∈ KH.cellMon S I) :
    ∃ e : K → ℕ, IsMultiHomog u e := by
  induction hu using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, -, rfl⟩ := hf
    exact ⟨_, isMultiHomog_X k i⟩
  | one => exact ⟨0, isMultiHomog_one_zero⟩
  | mul f f' _ _ hf hf' =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hf'
    exact ⟨a + b, isMultiHomog_mul ha hb⟩

section Loc

variable {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M}

theorem mk_mem_locPart {T : Submonoid (MRingOver S ι)} {c : K → ℤ} (m : M) (t : T) (a : K → ℕ)
    (ht : IsMultiHomog (t : MRingOver S ι) a) (hm : m ∈ 𝓜 (c + fun k => (a k : ℤ))) :
    LocalizedModule.mk m t ∈ KH.locPart ι 𝓜 T c :=
  Submodule.subset_span ⟨m, t, a, ht, hm, rfl⟩

theorem locPart_normal (h𝓜 : KH.IsMGraded S ι 𝓜) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T M} (hx : x ∈ KH.locPart ι 𝓜 T c) :
    ∃ (m : M) (t : T) (a : K → ℕ), IsMultiHomog (t : MRingOver S ι) a ∧
      m ∈ 𝓜 (c + fun k => (a k : ℤ)) ∧ x = LocalizedModule.mk m t := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, 1, 0, isMultiHomog_one_zero, zero_mem _, (LocalizedModule.zero_mk 1).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    obtain ⟨m', t', a', ht', hm', rfl⟩ := hy
    have e : ∀ a a' : K → ℕ, (c + fun k => ((a + a') k : ℤ)) =
        (c + fun k => (a k : ℤ)) + fun k => (a' k : ℤ) := by
      intro a a'
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    refine ⟨t' • m + t • m', t * t', a + a', isMultiHomog_mul ht ht', add_mem ?_ ?_,
      LocalizedModule.mk_add_mk⟩
    · rw [Submonoid.smul_def, e]
      exact h𝓜.2 _ _ _ _ ht' hm
    · rw [Submonoid.smul_def, add_comm a a', e]
      exact h𝓜.2 _ _ _ _ ht hm'
  | smul s x _ hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    exact ⟨s • m, t, a, ht, Submodule.smul_mem _ s hm, LocalizedModule.smul'_mk s m t⟩

theorem smul_mem_locPart (h𝓜 : KH.IsMGraded S ι 𝓜) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {p : MRingOver S ι} {a : K → ℕ} (hp : IsMultiHomog p a) {x : LocalizedModule T M}
    (hx : x ∈ KH.locPart ι 𝓜 T c) : p • x ∈ KH.locPart ι 𝓜 T (c + fun k => (a k : ℤ)) := by
  obtain ⟨m, t, b, ht, hm, rfl⟩ := locPart_normal h𝓜 hx
  rw [LocalizedModule.smul'_mk]
  refine mk_mem_locPart _ t b ht ?_
  have e : ((c + fun k => (a k : ℤ)) + fun k => (b k : ℤ)) =
      (c + fun k => (b k : ℤ)) + fun k => (a k : ℤ) := by
    funext k
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact h𝓜.2 _ _ _ _ hp hm

abbrev locMap {N : Type*} [AddCommGroup N] [Module (MRingOver S ι) N] (T : Submonoid (MRingOver S ι))
    (f : M →ₗ[MRingOver S ι] N) : LocalizedModule T M →ₗ[MRingOver S ι] LocalizedModule T N :=
  IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) f

theorem locMap_mk {N : Type*} [AddCommGroup N] [Module (MRingOver S ι) N] {T : Submonoid (MRingOver S ι)}
    (f : M →ₗ[MRingOver S ι] N) (m : M) (t : T) :
    locMap T f (LocalizedModule.mk m t) = LocalizedModule.mk (f m) t := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

theorem mem_of_map_mem {M' : Type*} [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
    [IsScalarTower S (MRingOver S ι) M'] {𝓜' : (K → ℤ) → Submodule S M'} (h𝓜' : KH.IsMGraded S ι 𝓜')
    (h𝓜 : KH.IsMGraded S ι 𝓜) {g : M' →ₗ[MRingOver S ι] M} (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g)
    (hinj : Function.Injective g) {c : K → ℤ} {m' : M'} (hm : g m' ∈ 𝓜 c) : m' ∈ 𝓜' c := by
  classical
  have key : ∃ y ∈ 𝓜' c, g m' - g y ∈ ⨆ (j) (_ : j ≠ c), 𝓜 j := by
    have hx : m' ∈ ⨆ j, 𝓜' j := by
      rw [h𝓜'.1.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (motive := fun x => ∃ y ∈ 𝓜' c, g x - g y ∈ ⨆ (j) (_ : j ≠ c), 𝓜 j)
      𝓜' hx ?_ ?_ ?_
    · intro j x hx
      by_cases hj : j = c
      · subst hj
        exact ⟨x, hx, by rw [sub_self]; exact zero_mem _⟩
      · refine ⟨0, zero_mem _, ?_⟩
        rw [map_zero, sub_zero]
        exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hg j x hx))
    · exact ⟨0, zero_mem _, by rw [map_zero, sub_zero]; exact zero_mem _⟩
    · intro x₁ x₂ h₁ h₂
      obtain ⟨y₁, hy₁, e₁⟩ := h₁
      obtain ⟨y₂, hy₂, e₂⟩ := h₂
      refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
      have : g (x₁ + x₂) - g (y₁ + y₂) = (g x₁ - g y₁) + (g x₂ - g y₂) := by
        simp only [map_add]
        abel
      rw [this]
      exact add_mem e₁ e₂
  obtain ⟨y, hy, hd⟩ := key
  have hc : g m' - g y ∈ 𝓜 c := sub_mem hm (hg c y hy)
  have h0 : g m' - g y = 0 := Submodule.disjoint_def.mp (h𝓜.1.submodule_iSupIndep c) _ hc hd
  rw [sub_eq_zero] at h0
  rw [hinj h0]
  exact hy

end Loc

theorem proof (hSES : KH.CechSESStatement) (hMap : KH.CechMapDegStatement) : GenSESStep.Statement := by
  intro S _ K _ _ ι _ _ M' _ _ _ _ M _ _ _ _ M'' _ _ _ _ 𝓜' 𝓜 𝓜'' g h h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex d
    hH1 hgen' hgen'' I x hx

  obtain ⟨m₀, t₀, a₀, ht₀, hm₀, rfl⟩ := locPart_normal h𝓜 hx
  have hx'' : LocalizedModule.mk (h m₀) t₀ ∈ KH.locPart ι 𝓜'' (KH.cellMon S I.1) d :=
    mk_mem_locPart _ _ a₀ ht₀ (hh _ _ hm₀)
  obtain ⟨t₁, a₁, r, p, z'', ht₁T, ht₁, hp, hz'', e₁⟩ := hgen'' I _ hx''

  have hlift := fun j => (hSES S K ι M' M M'' 𝓜' 𝓜 𝓜'' g h h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex d
    0).2.2.2.2.1 hH1 (z'' j) (hz'' j)
  choose z hz hzmap using hlift
  have hzI : ∀ j, z j I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d :=
    fun j => Submodule.mem_pi.mp (hz j).1 I (Set.mem_univ _)
  have hzh : ∀ j, locMap (KH.cellMon S I.1) h (z j I) = z'' j I := fun j => congrFun (hzmap j) I

  obtain ⟨y, hy_def⟩ : ∃ y, y = t₁ • LocalizedModule.mk m₀ t₀ - ∑ j, p j • z j I := ⟨_, rfl⟩
  have hLy : locMap (KH.cellMon S I.1) h y = 0 := by
    rw [hy_def, map_sub, map_smul, map_sum, locMap_mk, e₁, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hzh]
  have hyloc : y ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) (d + fun k => (a₁ k : ℤ)) := by
    rw [hy_def]
    exact sub_mem (smul_mem_locPart h𝓜 ht₁ hx)
      (Submodule.sum_mem _ fun j _ => smul_mem_locPart h𝓜 (hp j) (hzI j))
  obtain ⟨m, s, b, hs, hm, hys⟩ := locPart_normal h𝓜 hyloc

  have h0 : LocalizedModule.mk (h m) s = 0 := by rw [← locMap_mk, ← hys]; exact hLy
  rw [← LocalizedModule.zero_mk (1 : KH.cellMon S I.1), LocalizedModule.mk_eq] at h0
  obtain ⟨u, hu⟩ := h0
  rw [one_smul, smul_zero, smul_zero] at hu
  have hker : u • m ∈ LinearMap.ker h := by
    rw [LinearMap.mem_ker, Submonoid.smul_def, map_smul, ← Submonoid.smul_def]
    exact hu
  rw [← hex] at hker
  obtain ⟨m', hm'⟩ := hker
  obtain ⟨e, hue⟩ := cellMon_homog u.2
  have hm'deg : m' ∈ 𝓜' (((d + fun k => (a₁ k : ℤ)) + fun k => (b k : ℤ)) + fun k => (e k : ℤ)) := by
    refine mem_of_map_mem h𝓜' h𝓜 hg hinj ?_
    rw [hm', Submonoid.smul_def]
    exact h𝓜.2 _ _ _ _ hue hm

  let v : KH.cellMon S I.1 := ⟨t₁, ht₁T⟩ * u * s
  have hv : IsMultiHomog (v : MRingOver S ι) (a₁ + e + b) := isMultiHomog_mul (isMultiHomog_mul ht₁ hue) hs
  have hy'' : LocalizedModule.mk m' v ∈ KH.locPart ι 𝓜' (KH.cellMon S I.1) d := by
    refine mk_mem_locPart _ v _ hv ?_
    have edeg : (d + fun k => ((a₁ + e + b) k : ℤ)) =
        ((d + fun k => (a₁ k : ℤ)) + fun k => (b k : ℤ)) + fun k => (e k : ℤ) := by
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    rw [edeg]
    exact hm'deg
  obtain ⟨t₂, a₂, r', p', z', ht₂T, ht₂, hp', hz', e₂⟩ := hgen' I _ hy''

  have hw : ∀ l, KH.cechMap S ι g 0 (z' l) ∈ KH.cechZc ι 𝓜 d 0 := by
    intro l
    obtain ⟨h1, h2⟩ := hMap S K ι M' M 𝓜' 𝓜 g d 0 hg
    refine ⟨h1 _ (hz' l).1, LinearMap.mem_ker.mpr ?_⟩
    rw [← LinearMap.comp_apply, h2, LinearMap.comp_apply, LinearMap.mem_ker.mp (hz' l).2, map_zero]
  have hgv : (t₁ : MRingOver S ι) • locMap (KH.cellMon S I.1) g (LocalizedModule.mk m' v) = y := by
    rw [locMap_mk, LocalizedModule.smul'_mk, hm', hys]
    have : (t₁ : MRingOver S ι) • (u • m) = ((⟨t₁, ht₁T⟩ * u : KH.cellMon S I.1) • m) := by
      rw [Submonoid.smul_def, Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    rw [this]
    exact LocalizedModule.mk_cancel_common_left _ _ _
  have hgy : t₂ • y = t₁ • ∑ l, p' l • KH.cechMap S ι g 0 (z' l) I := by
    rw [← hgv, ← mul_smul, mul_comm, mul_smul, ← map_smul, e₂, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
    rw [map_smul]
    rfl
  refine ⟨t₂ * t₁, a₂ + a₁, r + r', Fin.append (fun j => t₂ * p j) (fun l => t₁ * p' l),
    Fin.append z (fun l => KH.cechMap S ι g 0 (z' l)), mul_mem ht₂T ht₁T, isMultiHomog_mul ht₂ ht₁,
    fun j => ?_, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun l => ?_) j
    · rw [Fin.append_left]
      exact isMultiHomog_mul ht₂ (hp j)
    · rw [Fin.append_right, add_comm]
      exact isMultiHomog_mul ht₁ (hp' l)
  · refine Fin.addCases (fun j => ?_) (fun l => ?_) j
    · rw [Fin.append_left]
      exact hz j
    · rw [Fin.append_right]
      exact hw l
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have hyeq : t₁ • LocalizedModule.mk m₀ t₀ = y + ∑ j, p j • z j I := by
      rw [hy_def, sub_add_cancel]
    rw [mul_smul, hyeq, smul_add, hgy, Finset.smul_sum, Finset.smul_sum, add_comm]
    simp only [smul_smul]

end GenSESStep

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphChangeOfModel
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GraphChangeOfModel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K₂ : Type} {ι₂ : K₂ → Type}

theorem exists_form_not_mem {P : Ideal (MRing ι)} {d : ℕ} {g : (Σ k, ι₂ k) → MRing ι} (hP : IsArithVar P d)
    (hBP : IsBasePtFree P g) : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P := by
  intro k₂
  by_contra hall
  push Not at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  choose i hi using hrel
  obtain ⟨N, hN⟩ := hBP k₂ i
  have hle : Ideal.span (Set.range fun j : ι₂ k₂ => g ⟨k₂, j⟩) ≤ P :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle] at hN
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp (hprime.mem_of_pow_mem N hN)
  exact hi k hk

end GraphChangeOfModel

open GraphChangeOfModel IndefiniteRowSideFullHecke.Inter in

theorem GraphChangeOfModel.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hGF : GenFibreExistsStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hIso : IsomInvariance.Statement) (hGI : GraphIsometricForms.Statement) : GraphChangeOfModel.Statement := by
  intro I hI K _ ι _ K₂ _ ι₂ _ P d g δ G J L L₁ hP hg hBP hImg hJ hL hL₁ ha hh
  obtain ⟨hΓ, himg, hdeg⟩ := hGr K ι K₂ ι₂ P d g δ hP hg (exists_form_not_mem hP hBP)
  obtain ⟨G'⟩ := hGF K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV _ d isBlockMap_inl hΓ
  obtain ⟨J', hJ', -⟩ := hEU G'.Φ _ (fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂))
  have e1 := hAI3 I hI K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV _ d G' J' L₁
    (fun j => pullHerm isBlockMap_inl (L₁ j)) isBlockMap_inl hΓ (by rw [himg]; exact hP) hJ' hL₁
    (fun j => isPullHerm_pullHerm _ _)
  have e2 := hAI3 I hI K₂ ι₂ (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inr inrV _ d G J L
    (fun j => pullHerm isBlockMap_inr (L j)) isBlockMap_inr hΓ hImg hJ hL
    (fun j => isPullHerm_pullHerm _ _)
  have e3 := hIso (K ⊕ K₂) (Sum.elim ι ι₂) (I (K ⊕ K₂) (Sum.elim ι ι₂)) (hI _ _) _ d
    (fun j => pullHerm isBlockMap_inl (L₁ j)) (fun j => pullHerm isBlockMap_inr (L j)) hΓ
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inl (isPullHerm_pullHerm _ _) (hL₁ j))
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inr (isPullHerm_pullHerm _ _) (hL j))
    (fun j => hGI K ι K₂ ι₂ P d g δ (L₁ j) (L j) _ _ hP hg hBP (ha j) (hh j) (isPullHerm_pullHerm _ _)
      (isPullHerm_pullHerm _ _))
  rw [hdeg G' J' hJ', himg] at e1
  rw [← e2, ← e3, e1]
  simp

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedKleimanLow
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleimanLow.exists_monomial {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (hP : P.IsPrime) (hrel : IsRelevant P) (a : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) ∧ (monomial μ 1 : MRing ι) ∉ P ∧
      IsMultiHomog (monomial μ 1 : MRing ι) a := by
  classical
  choose c hc using hrel
  let μ : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k := fun k => by simp [μ]
  refine ⟨μ, hμ, fun hmem => ?_, fun m hm k => ?_⟩
  · rw [monomial_eq, map_one, one_mul, Finsupp.prod, hP.prod_mem_iff] at hmem
    obtain ⟨p, hp, hXp⟩ := hmem
    have hp2 : p.2 = c p.1 := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hp) (by simp [μ, h])
    obtain ⟨k, i⟩ := p
    obtain rfl : i = c k := hp2
    exact hc k (hP.mem_of_pow_mem _ hXp)
  · rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
    exact hμ k

theorem MixedKleimanLow.proof (hI : IntegralAgainstPositive.Statement)
    (hK : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg) : MixedKleimanLow.Statement := by
  classical
  intro d hd K _ ι _ P P0 M A a II hII h1 hP hP0 hMs hMn hMc hMW hAa hAs hAb hAc j hj
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  change MixedKleiman.AtDim n at hd
  let L : Fin n → HermLine ι := fun i => if (i : ℕ) < j then M else A
  have hsnoc : (fun i : Fin (n + 1) => if (i : ℕ) < j then M else A) = Fin.snoc L A := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last, if_neg (by simp; omega)]
    · rw [Fin.snoc_castSucc]; rfl
  have hLs : ∀ i, IsSemipositiveRel P0 P (L i) := fun i => by
    simp only [L]; split_ifs <;> assumption
  obtain ⟨μ, hμ, hsP, hsh⟩ := MixedKleimanLow.exists_monomial P hP.2.1.1 hP.2.1.2.2 a
  have hAk : ∀ k, A.a k = a k := fun k => by rw [hAa]

  have hpts : ∀ {W : Ideal (MRing ι)}, P ≤ W → mcPts W ⊆ mcPts P := fun hPW z hz => ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
  have hchar : ∀ W W' : Ideal (MRing ι), W ≤ W' → charOf W ≠ 0 → charOf W' ≠ 0 := by
    intro W W' hle hW hW'
    apply hW
    unfold charOf at hW' ⊢
    rw [Int.natAbs_eq_zero, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero] at hW' ⊢
    exact le_bot_iff.mp (hW' ▸ Ideal.comap_mono hle)
  rw [hsnoc, (hII K ι).2.2 P n L A _ a hP (fun i => (hLs i).1) hAs.1 hAk hsh hsP]
  unfold recR
  refine sub_nonneg.mpr (le_trans ?_ (finsum_nonneg fun W => finsum_nonneg fun hW => ?_))
  ·
    refine hI K ι P P0 n L _ hP0 hLs fun z hz => ?_
    have hpos := A.pos z hz.1
    unfold logNorm
    refine Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le) ((div_le_one hpos).mpr ?_)
    rw [map_monomial, eval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    exact hAb z hz μ hμ
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    obtain ⟨hH, hV⟩ := divSuppArith K ι P n A _ W hP ⟨a, hAk, hsh, hsP⟩ hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    split_ifs with hWh
    ·
      have hWv := hH hWh
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact absurd hWv (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι W)
      exact hd K ι W P0 M A a II hII hn hWv (hP0.trans hPW)
        ⟨hMs.1, fun z hz => hMs.2 z (hpts hPW hz)⟩ (fun W' h1 h2 => hMn W' h1 (hPW.trans h2)) hMc
        (fun W' h1 h2 => hMW W' h1 (hPW.trans h2)) hAa ⟨hAs.1, fun z hz => hAs.2 z (hpts hPW hz)⟩
        (fun z hz => hAb z (hpts hPW hz)) hAc j (by omega)
    ·
      by_cases hc : charOf W = 0
      · simp [hc]
      have hg : 0 ≤ geoNum n W (fun i => (L i).a) := by
        refine hK K ι W n _ (hV hWh).1 hc (hV hWh).2.2 fun i => ?_
        intro W' h1 h2 h3
        simp only [L]
        split_ifs
        · exact hMn W' h1 (hPW.trans h2) (hchar W W' h2 hc) h3
        · rw [hAa]
          exact ProjLine.nefOnFibres_of_nonneg W' _ (fun k => by positivity) W' h1 le_rfl (hchar W W' h2 hc) h3
      exact mul_nonneg (by exact_mod_cast hg) (Real.log_natCast_nonneg _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefShiftPolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

theorem NefShiftPolynomial.proof (hF : FujitaGeneric.Statement) (hC : ChartLatQCech.Statement)
    (hE : EulerHilbert.Statement) (hL : EventualPolyLine.Statement) : NefShiftPolynomial.Statement := by
  intro K _ ι _ Ω _ _ y D a _ hV _ hN
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  obtain ⟨hQ, hdim⟩ := ShiftDegreePolynomial.genericFibre hV
  set Q := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) with hQdef
  obtain ⟨m, hm⟩ := hF K ι (mCoordIdeal y) D a hV hN
  obtain ⟨p, a₀, hpdeg, hp⟩ :=
    MultigradedHilbertPolynomial.proof EventualPolynomial.proof ℚ K ι Q D hQ hdim
  obtain ⟨r, hrdeg, hrcoef, hr⟩ := hL K D (hilbFn Q) p a₀ a (fun _ => (m : ℤ)) hpdeg hp
  refine ⟨m, r, hrdeg, ?_, Eventually.of_forall fun n => ?_⟩
  · have hH : ∀ i j : DecidableEq K, @hilbFn K i ι ℚ _ Q = @hilbFn K j ι ℚ _ Q := fun i j => by
      rw [Subsingleton.elim i j]
    have hg : genDeg (mCoordIdeal y) D a = eventualValue (mixedDiff (fun _ : Fin D => a) (hilbFn Q)) :=
      congrArg (fun h => eventualValue (mixedDiff (fun _ : Fin D => a) h)) (hH _ _)
    rw [hrcoef, hg]
  · obtain ⟨e⟩ := hC K ι Ω y (D + 1) ((n : ℤ) • a + fun _ => (m : ℤ)) hV
    rw [e.finrank_eq, ← hr n, ← hE ℚ K ι Q p a₀ hQ hp _ (hm n)]
    norm_cast

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphFibreRatio
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGraphFibreRatio.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
    ∀ (G : GenFibre (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M))) (k : K) (i j : ι k),
      G.x' ⟨Sum.inl k, j⟩ ≠ 0 → G.x' ⟨Sum.inl k, i⟩ / G.x' ⟨Sum.inl k, j⟩ ∈ (algebraMap G.Φ G.Φ').range

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartNakayamaGen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartNakayamaGen.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (d : K → ℤ),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → P.IsPrime → IsMultiHomogIdeal P →
    ∀ I : KH.Cell K ι 0, (∀ k, ∀ i ∈ I.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    (∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d, ∃ z ∈ KH.cechZc ι 𝓜 d 0,
      x - z I ∈ locIdealPart 𝓜 (KH.cellMon S I.1) P d) →
    ∃ (f : MRingOver S ι) (δ : K → ℕ), IsMultiHomog f δ ∧ f ∉ P ∧ GenNear S ι 𝓜 d f δ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

