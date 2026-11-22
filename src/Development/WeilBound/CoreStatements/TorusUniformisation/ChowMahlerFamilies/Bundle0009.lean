import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0007
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinGradedFrameIff

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFamConstr
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_fam_constr

open ReciprocityTheory.ChartRestriction.G.Geo (exists_pow_mul_mem_chartRing div_mem_chartRing)

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} {x : (Σ k, ι k) → Ω}
variable {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

theorem mono {Γ : (∀ k, ι k) → AddSubgroup V} (h : IsLatFamily o x Γ) {s t : ∀ k, ι k}
    (ht : mseg x t ≠ 0) {v : V} {m m' : ℕ} (hm : m ≤ m') (hv : (mseg x s / mseg x t) ^ m • v ∈ Γ t) :
    (mseg x s / mseg x t) ^ m' • v ∈ Γ t := by
  rw [← Nat.sub_add_cancel hm, pow_add, mul_smul]
  exact h.1 t ht _ (pow_mem (div_mem_chartRing (mseg x) t s) _) _ hv

theorem fam_sub (U : Submodule Ω V) : IsLatFamily o x (fun _ => U.toAddSubgroup) :=
  ⟨fun _ _ a _ _ hv => U.smul_mem a hv, fun _ _ _ _ _ hv => ⟨0, U.smul_mem _ hv⟩⟩

theorem fam_top : IsLatFamily o x (fun _ => (⊤ : AddSubgroup V)) :=
  ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => ⟨0, trivial⟩⟩

theorem fam_bot : IsLatFamily o x (fun _ => (⊥ : AddSubgroup V)) := fam_sub ⊥

theorem fam_sup {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => A c ⊔ B c) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    rw [smul_add]
    exact AddSubgroup.add_mem_sup (hA.1 s hs a ha y hy) (hB.1 s hs a ha z hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
    obtain ⟨m', hm'⟩ := hB.2 s t hs ht z hz
    refine ⟨m + m', ?_⟩
    rw [smul_add]
    exact AddSubgroup.add_mem_sup (mono hA ht (Nat.le_add_right _ _) hm)
      (mono hB ht (Nat.le_add_left _ _) hm')

theorem fam_inf {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => A c ⊓ B c) := by
  refine ⟨fun s hs a ha v hv => ⟨hA.1 s hs a ha v hv.1, hB.1 s hs a ha v hv.2⟩,
    fun s t hs ht v hv => ?_⟩
  obtain ⟨m, hm⟩ := hA.2 s t hs ht v hv.1
  obtain ⟨m', hm'⟩ := hB.2 s t hs ht v hv.2
  exact ⟨m + m', mono hA ht (Nat.le_add_right _ _) hm, mono hB ht (Nat.le_add_left _ _) hm'⟩

theorem fam_map {A : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (f : V →+ V₁)
    (hf : ∀ (a : Ω) v, f (a • v) = a • f v) : IsLatFamily o x (fun c => (A c).map f) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨_, hA.1 s hs a ha y hy, hf a y⟩
  · obtain ⟨y, hy, rfl⟩ := hv
    obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
    exact ⟨m, _, hm, hf _ y⟩

theorem fam_comap {A : (∀ k, ι k) → AddSubgroup V₁} (hA : IsLatFamily o x A) (f : V →+ V₁)
    (hf : ∀ (a : Ω) v, f (a • v) = a • f v) : IsLatFamily o x (fun c => (A c).comap f) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · rw [AddSubgroup.mem_comap, hf]
    exact hA.1 s hs a ha _ hv
  · obtain ⟨m, hm⟩ := hA.2 s t hs ht _ hv
    exact ⟨m, by rw [AddSubgroup.mem_comap, hf]; exact hm⟩

theorem fam_prod {A : (∀ k, ι k) → AddSubgroup V} {B : (∀ k, ι k) → AddSubgroup V₁}
    (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => (A c).prod (B c)) := by
  refine ⟨fun s hs a ha v hv => ⟨hA.1 s hs a ha _ hv.1, hB.1 s hs a ha _ hv.2⟩,
    fun s t hs ht v hv => ?_⟩
  obtain ⟨m, hm⟩ := hA.2 s t hs ht _ hv.1
  obtain ⟨m', hm'⟩ := hB.2 s t hs ht _ hv.2
  exact ⟨m + m', mono hA ht (Nat.le_add_right _ _) hm, mono hB ht (Nat.le_add_left _ _) hm'⟩

theorem mem_stdLat (R : Subalgebra o Ω) {J : Type} (v : J → Ω) : v ∈ stdLat R J ↔ ∀ j, v j ∈ R :=
  ⟨fun h j => h j trivial, fun h j _ => h j⟩

theorem fam_std (J : Type) [Fintype J] :
    IsLatFamily o x (fun c => stdLat (chartRing o (mseg x) c) J) := by
  refine ⟨fun s _ a ha v hv => ?_, fun s t hs _ v hv => ?_⟩
  · rw [mem_stdLat] at hv ⊢
    exact fun j => mul_mem ha (hv j)
  · rw [mem_stdLat] at hv
    choose m hm using fun j => exists_pow_mul_mem_chartRing (mseg x) s t hs (hv j)
    refine ⟨∑ q, m q, (mem_stdLat _ _).2 fun q => ?_⟩
    have hle : m q ≤ ∑ q, m q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [Pi.smul_apply, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) (hm q)

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

def FG (R : Subalgebra o Ω) (L : AddSubgroup V) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (g : I → V), (∀ i, g i ∈ L) ∧
    ∀ e ∈ L, ∃ a : I → Ω, (∀ i, a i ∈ R) ∧ ∑ i, a i • g i = e

theorem fg_of_locFree {R : Subalgebra o Ω} {r : ℕ} {L : AddSubgroup V} (h : LocFree R r L) :
    FG R L := by
  let L' : Submodule R V := { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := r) h
  exact ⟨_, inferInstance, fun i => v i, fun i => (v i).2,
    fun e he => ⟨fun i => φ i e, fun i => hφ i e he, hv e⟩⟩

theorem fg_comap {R : Subalgebra o Ω} {L : AddSubgroup V₁} (h : FG R L) (f : V →ₗ[Ω] V₁)
    (hf : Function.Injective f) (hS : Summand L (LinearMap.range f)) :
    FG R (L.comap f.toAddMonoidHom) := by
  obtain ⟨I, hI, g, hg, hL⟩ := h
  obtain ⟨ρ, h1, h2, h3⟩ := hS
  choose y hy using fun i => h1 (g i)
  refine ⟨I, hI, y, fun i => ?_, fun e he => ?_⟩
  · change f (y i) ∈ L
    rw [hy]
    exact h3 _ (hg i)
  · obtain ⟨a, ha, hs⟩ := hL (f e) he
    refine ⟨a, ha, hf ?_⟩
    rw [← h2 (f e) ⟨e, rfl⟩, ← hs]
    simp only [map_sum, map_smul, hy]

theorem fam_dual {m : ℕ} {A : (∀ k, ι k) → AddSubgroup (Fin m → Ω)} (hA : IsLatFamily o x A)
    (hfg : ∀ c, mseg x c ≠ 0 → FG (chartRing o (mseg x) c) (A c)) :
    IsLatFamily o x (fun c => dotDual (chartRing o (mseg x) c) (A c)) := by
  refine ⟨fun s _ a ha w hw => ?_, fun s t hs ht w hw => ?_⟩
  · rw [mem_dotDual] at hw ⊢
    intro v hv
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha (hw v hv)
  · rw [mem_dotDual] at hw
    obtain ⟨I, hI, g, hg, hL⟩ := hfg t ht
    have key : ∀ i, ∃ k : ℕ, (mseg x s / mseg x t) ^ k * (g i ⬝ᵥ w) ∈ chartRing o (mseg x) t := by
      intro i
      obtain ⟨k, hk⟩ := hA.2 t s ht hs _ (hg i)
      obtain ⟨k', hk'⟩ := exists_pow_mul_mem_chartRing (mseg x) s t hs (hw _ hk)
      refine ⟨k', ?_⟩
      have hu : (mseg x s / mseg x t) ^ k * (mseg x t / mseg x s) ^ k = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm (mseg x s), div_self (mul_ne_zero ht hs), one_pow]
      rw [smul_dotProduct, smul_eq_mul] at hk'
      have : (mseg x s / mseg x t) ^ k' * (g i ⬝ᵥ w) = (mseg x s / mseg x t) ^ k *
          ((mseg x s / mseg x t) ^ k' * ((mseg x t / mseg x s) ^ k * (g i ⬝ᵥ w))) := by
        linear_combination (-(mseg x s / mseg x t) ^ k' * (g i ⬝ᵥ w)) * hu
      rw [this]
      exact mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) hk'
    choose k hk using key
    refine ⟨∑ q, k q, (mem_dotDual _ _ _).2 fun v hv => ?_⟩
    obtain ⟨a, ha, rfl⟩ := hL v hv
    rw [sum_dotProduct]
    refine sum_mem fun q _ => ?_
    have hle : k q ≤ ∑ q, k q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add,
      mul_assoc]
    exact mul_mem (ha q) (mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) (hk q))

theorem linMap_inj {F : Type} [Zero F] [One F] (n : ℕ) (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) :
    Function.Injective (linMap n χ) := by
  rw [injective_iff_map_eq_zero]
  intro l hl
  funext j
  have := congrFun hl (Pi.single j 1)
  rw [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Finset.sum_eq_single j] at this
  · simpa [h1] using this
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi, h0]
  · simp

end PositivityTheory.Xgn.A_fam_constr

open PositivityTheory.Xgn.A_fam_constr in
theorem PositivityTheory.Xgn.t_fam_constr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) ∧ ∀ τ, IsLatFamily O x (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ (∀ i, IsLatFamily O x (fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) ∧ IsLatFamily O x (fun c => (D c).stepGraph τ (fun a => algebraMap O Ω (χ τ a)) i)) ∧ (∀ i, IsLatFamily O x (fun c => (D c).kk τ i)) ∧ IsLatFamily O x (fun c => dotDual (chartRing O (mseg x) c) ((D c).lie τ)) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → IsLatFamily O x (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ IsLatFamily O x (fun c => (D c).imH (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)))) := by
  classical
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ F _ _ _ n Sg _ r s p _ w χ φ D hD
  have hl1 : IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) :=
    fam_sup hD.famM (fam_map (fam_std _) _ fun a v => smul_comm _ _ _)
  refine ⟨hl1, fun τ => ?_⟩
  obtain ⟨hlie, -, -, -, -, hDel, hTh⟩ := hD.fam τ
  have haf : IsLatFamily O x
      (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) :=
    fam_comap hl1 _ fun a v => (linMap n (fun a => algebraMap O Ω (χ τ a))).map_smul a v
  refine ⟨haf, fun i => ⟨?_, ?_⟩, fun i => ?_, ?_, fun hG => ?_⟩
  · exact fam_comap (fam_sup hD.famM (fam_sub _)) _
      fun a v => (LinearMap.toSpanSingleton Ω _ _).map_smul a v
  · exact fam_comap (fam_sup hTh (fam_prod (fam_sub _) fam_bot)) _
      fun a v => Prod.ext ((LinearMap.toSpanSingleton Ω _ _).map_smul a v.1) rfl
  · exact fam_map (fam_inf hTh (fam_prod (fam_sub _) fam_top)) _ fun a v => rfl
  · exact fam_dual hlie fun c hc => fg_of_locFree ((hD.base c hc).free τ).1
  · have hh : IsLatFamily O x
        (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) := by
      refine fam_dual haf fun c hc => fg_comap (fg_of_locFree (hG c hc).l1) _
        (linMap_inj n _ ?_ ?_) ((hG c hc).lin τ)
      · simp [(hD.char.2.2.2.2 τ).1]
      · simp [(hD.char.2.2.2.2 τ).2]
    exact ⟨hh, fam_map (fam_inf hDel (fam_prod hh fam_top)) _ fun a v => rfl⟩
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlagframeBasis
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_flagframe_basis

variable {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V] {N : ℕ}

theorem repr_expand (w u : Module.Basis (Fin N) Ω V) (v : V) (j : Fin N) :
    w.repr v j = ∑ q, u.repr v q * w.repr (u q) j := by
  conv_lhs => rw [← u.sum_repr v]
  exact GradedFrameCharacterisation.repr_sum_smul w _ _ j

theorem top_coord (w u : Module.Basis (Fin N) Ω V) (hup : ∀ i j, i < j → w.repr (u i) j = 0)
    (v : V) (i : Fin N) (hv : ∀ j, i < j → u.repr v j = 0) :
    (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = u.repr v i * w.repr (u i) i := by
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [repr_expand w u]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : i < q
    · rw [hv q hq, zero_mul]
    · rw [hup q j (lt_of_le_of_lt (not_lt.mp hq) hj), mul_zero]
  · rw [repr_expand w u]
    refine Finset.sum_eq_single i (fun q _ hq => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hq with h | h
    · rw [hup q i h, mul_zero]
    · rw [hv q h, zero_mul]

theorem vanish_above (w u : Module.Basis (Fin N) Ω V) (hup : ∀ i j, i < j → w.repr (u i) j = 0)
    (hd : ∀ i, w.repr (u i) i ≠ 0) (v : V) (i : Fin N) (hv : ∀ j, i < j → w.repr v j = 0) :
    ∀ j, i < j → u.repr v j = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hne : (Finset.univ.filter (fun j => i < j ∧ u.repr v j ≠ 0)).Nonempty := by
    obtain ⟨j, hj, hj'⟩ := hcon
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hj'⟩⟩
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image _ id hne
  have hm := (Finset.mem_filter.mp hmS).2
  have habove : ∀ j, m < j → u.repr v j = 0 := by
    intro j hj
    by_contra h0
    have hjS := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hm.1 hj, h0⟩)
    exact absurd hjS (not_le.mpr hj)
  have ht := top_coord w u hup v m habove
  have h0 := hv m hm.1
  rw [ht.2] at h0
  exact mul_ne_zero hm.2 (hd m) h0

theorem exists_basis (w : Module.Basis (Fin N) Ω V) (f : Fin N → V)
    (hup : ∀ i j, i < j → w.repr (f i) j = 0) (hd : ∀ i, w.repr (f i) i ≠ 0) :
    ∃ u : Module.Basis (Fin N) Ω V, ∀ i, u i = f i := by
  classical
  rcases isEmpty_or_nonempty (Fin N) with hN | hN
  · exact ⟨w, fun i => isEmptyElim i⟩
  · have hli : LinearIndependent Ω f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      by_contra hcon
      push_neg at hcon
      have hne : (Finset.univ.filter (fun j => g j ≠ 0)).Nonempty := by
        obtain ⟨j, hj⟩ := hcon
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image _ id hne
      have hm := (Finset.mem_filter.mp hmS).2
      have h0 := congrArg (fun v => w.repr v m) hg
      simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero,
        Finsupp.coe_zero, Pi.zero_apply] at h0
      rw [Finset.sum_eq_single m] at h0
      · exact mul_ne_zero hm (hd m) h0
      · intro q _ hqm
        rcases lt_or_gt_of_ne hqm with h | h
        · rw [hup q m h, mul_zero]
        · have hgq : g q = 0 := by
            by_contra hq
            exact absurd (hmax q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩)) (not_le.mpr h)
          rw [hgq, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ m) h
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hli ?_, fun i => ?_⟩
    · rw [Module.finrank_eq_card_basis w]
    · rw [coe_basisOfLinearIndependentOfCardEqFinrank]

theorem coords_mem {O : Type*} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) (L : AddSubgroup V)
    (u : Module.Basis (Fin N) Ω V) (hst : ∀ a ∈ R, ∀ i, a • u i ∈ L)
    (htop : ∀ v ∈ L, ∀ i, (∀ j, i < j → u.repr v j = 0) → u.repr v i ∈ R) :
    ∀ v ∈ L, ∀ i, u.repr v i ∈ R := by
  classical
  have main : ∀ k : ℕ, ∀ v ∈ L, (∀ j : Fin N, k ≤ j.val → u.repr v j = 0) → ∀ i, u.repr v i ∈ R := by
    intro k
    induction k with
    | zero =>
      intro v _ hv i
      rw [hv i (Nat.zero_le _)]
      exact R.zero_mem
    | succ k ih =>
      intro v hvL hv
      by_cases hk : k < N
      · have ha : u.repr v ⟨k, hk⟩ ∈ R :=
          htop v hvL ⟨k, hk⟩ (fun j hj => hv j (Nat.succ_le_of_lt (Fin.lt_def.mp hj)))
        have hv'L : v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩ ∈ L := L.sub_mem hvL (hst _ ha _)
        have hrep : ∀ j, u.repr (v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩) j =
            u.repr v j - u.repr v ⟨k, hk⟩ * (if (⟨k, hk⟩ : Fin N) = j then 1 else 0) := by
          intro j
          rw [map_sub, map_smul, Module.Basis.repr_self, Finsupp.coe_sub, Pi.sub_apply, Finsupp.smul_apply,
            Finsupp.single_apply, smul_eq_mul]
        have hv' : ∀ j : Fin N, k ≤ j.val → u.repr (v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩) j = 0 := by
          intro j hj
          rw [hrep j]
          rcases Nat.lt_or_eq_of_le hj with h | h
          · have hne : (⟨k, hk⟩ : Fin N) ≠ j := fun e => by
              rw [← e] at h
              exact lt_irrefl _ h
            rw [hv j h, if_neg hne, mul_zero, sub_zero]
          · have he : (⟨k, hk⟩ : Fin N) = j := Fin.ext h
            subst he
            rw [if_pos rfl, mul_one, sub_self]
        intro i
        have hi := ih _ hv'L hv' i
        rw [hrep i] at hi
        have h2 : u.repr v ⟨k, hk⟩ * (if (⟨k, hk⟩ : Fin N) = i then (1 : Ω) else 0) ∈ R := by
          split_ifs
          · rw [mul_one]
            exact ha
          · rw [mul_zero]
            exact R.zero_mem
        have h3 := R.add_mem hi h2
        rwa [sub_add_cancel] at h3
      · intro i
        exact ih v hvL (fun j hj => hv j (by have := j.isLt; omega)) i
  intro v hv i
  exact main N v hv (fun j hj => absurd j.isLt (not_lt.mpr hj)) i

end PositivityTheory.Xgn.A_flagframe_basis

open PositivityTheory.Xgn.A_flagframe_basis in
theorem PositivityTheory.Xgn.t_flagframe_basis : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b ↔ ∀ s, mseg x s ≠ 0 → ∃ u : Module.Basis (Fin N) Ω V, (∀ i j, i < j → w.repr (u i) j = 0) ∧ (∀ i, w.repr (u i) i = chartMon x s (b i)) ∧ ∀ v, v ∈ E.lat s ↔ ∀ i, u.repr v i ∈ chartRing O (mseg x) s := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ E w b
  have hmon : ∀ s, mseg x s ≠ 0 → ∀ d : K → ℤ, chartMon x s d ≠ 0 := by
    intro s hs d
    have hs' : ∏ k : K, x ⟨k, s k⟩ ≠ 0 := hs
    show ∏ k : K, x ⟨k, s k⟩ ^ d k ≠ 0
    exact Finset.prod_ne_zero_iff.mpr fun k _ =>
      zpow_ne_zero _ (Finset.prod_ne_zero_iff.mp hs' k (Finset.mem_univ _))
  constructor
  · intro hF s hs
    have hdeg : ∀ i, ∃ f ∈ E.lat s, (∀ j, i < j → w.repr f j = 0) ∧ w.repr f i = chartMon x s (b i) := by
      intro i
      have hmem : chartMon x s (b i) ∈ degLat O x (b i) s := ⟨1, Subalgebra.one_mem _, (one_mul _).symm⟩
      rw [← hF.graded s hs i] at hmem
      exact hmem
    choose f hfL hfup hfd using hdeg
    obtain ⟨u, hu⟩ := exists_basis w f hfup (fun i => by rw [hfd i]; exact hmon s hs (b i))
    have hup_u : ∀ i j, i < j → w.repr (u i) j = 0 := fun i j hij => by
      rw [hu i]
      exact hfup i j hij
    refine ⟨u, hup_u, fun i => by rw [hu i]; exact hfd i, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · refine coords_mem (chartRing O (mseg x) s) (E.lat s) u
        (fun a ha i => by rw [hu i]; exact E.stable s a ha _ (hfL i)) ?_ v hv
      intro v' hv' i hup'
      have ht := top_coord w u hup_u v' i hup'
      have hin : w.repr v' i ∈ degLat O x (b i) s := by
        rw [← hF.graded s hs i]
        exact ⟨v', hv', ht.1, rfl⟩
      obtain ⟨a, ha, hae⟩ := hin
      rw [ht.2, hu i, hfd i] at hae
      have hc := mul_right_cancel₀ (hmon s hs (b i)) hae
      rw [hc]
      exact ha
    · rw [← u.sum_repr v]
      exact AddSubgroup.sum_mem _ fun q _ => by
        rw [hu q]
        exact E.stable s _ (hv q) _ (hfL q)
  · intro hR
    refine ⟨fun s hs i => ?_⟩
    obtain ⟨u, hup, hdiag, hmem⟩ := hR s hs
    ext t
    constructor
    · rintro ⟨v, hv, habove, rfl⟩
      have hd : ∀ i, w.repr (u i) i ≠ 0 := fun i => by
        rw [hdiag i]
        exact hmon s hs (b i)
      have hu_above := vanish_above w u hup hd v i habove
      have ht := top_coord w u hup v i hu_above
      exact ⟨u.repr v i, (hmem v).mp hv i, by rw [ht.2, hdiag i]; rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a • u i, (hmem _).mpr fun j => ?_, fun j hj => ?_, ?_⟩
      · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        split_ifs
        · rw [mul_one]
          exact ha
        · rw [mul_zero]
          exact Subalgebra.zero_mem _
      · rw [map_smul, Finsupp.smul_apply, hup i j hj, smul_zero]
      · rw [map_smul, Finsupp.smul_apply, hdiag i, smul_eq_mul]
        rfl
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullLine
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_line
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)

variable {O : Type} [CommRing O] {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁]
  {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def comb (t : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => s (.inr k)

theorem mseg_join (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord (fun p => φ (x p)) z) s =
      φ (mseg x (restrictChart s)) * mseg z (fun k => s (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type, map_prod]
  rfl

theorem chartMon_join (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (a : K → ℤ) :
    chartMon (joinCoord (fun p => φ (x p)) z) s (pullDeg (K' := K') a) =
      φ (chartMon x (restrictChart s) a) := by
  simp only [chartMon, Fintype.prod_sum_type, pullDeg, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zpow_zero, Finset.prod_const_one, mul_one, map_prod, map_zpow₀]
  rfl

theorem map_mem (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0)
    (r : Ω) (hr : r ∈ chartRing O (mseg x) (restrictChart s)) :
    φ r ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s := by
  have hw : mseg z (fun k => s (.inr k)) ≠ 0 := by
    rw [mseg_join] at hs
    exact right_ne_zero_of_mul hs
  have hle : chartRing O (mseg x) (restrictChart s) ≤
      (chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s).comap φ := by
    unfold chartRing
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    have h : φ (mseg x t / mseg x (restrictChart s)) =
        mseg (joinCoord (fun p => φ (x p)) z) (comb t s) / mseg (joinCoord (fun p => φ (x p)) z) s := by
      rw [mseg_join φ x z (comb t s), mseg_join φ x z s, map_div₀]
      exact (mul_div_mul_right _ _ hw).symm
    have h2 := div_mem_chartRing (o := O) (mseg (joinCoord (fun p => φ (x p)) z)) s (comb t s)
    rw [← h] at h2
    exact h2
  exact hle hr

theorem main [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
    (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) (u : Ω) (a : K → ℤ)
    (A : (∀ k, ι k) → AddSubgroup Ω) (hA : IsLine O x u a A)
    (B : (∀ k : K ⊕ K', Sum.elim ι ι' k) → AddSubgroup Ω₁)
    (hB : ∀ s, mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0 → B s = AddSubgroup.closure
      {v | ∃ c ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s, ∃ e ∈ A (restrictChart s),
        v = c • φ e}) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0) (v : Ω₁) :
    v ∈ B s ↔ ∃ r ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s,
      v = r * (φ u * chartMon (joinCoord (fun p => φ (x p)) z) s (pullDeg (K' := K') a)) := by
  have hx : mseg x (restrictChart s) ≠ 0 := by
    rw [mseg_join] at hs
    intro h
    exact left_ne_zero_of_mul hs (by rw [h, map_zero])
  rw [hB s hs, chartMon_join, ← map_mul]
  constructor
  · intro hv
    induction hv using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, e, he, rfl⟩ := hw
      obtain ⟨r, hr, rfl⟩ := (hA _ hx e).1 he
      refine ⟨c * φ r, mul_mem hc (map_mem φ x z s hs r hr), ?_⟩
      rw [smul_eq_mul, map_mul, mul_assoc]
    | zero => exact ⟨0, zero_mem _, by rw [zero_mul]⟩
    | add w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨r₁, hr₁, rfl⟩ := h₁
      obtain ⟨r₂, hr₂, rfl⟩ := h₂
      exact ⟨r₁ + r₂, add_mem hr₁ hr₂, by rw [add_mul]⟩
    | neg w _ h =>
      obtain ⟨r, hr, rfl⟩ := h
      exact ⟨-r, neg_mem hr, by rw [neg_mul]⟩
  · rintro ⟨r, hr, rfl⟩
    exact AddSubgroup.subset_closure ⟨r, hr, _, (hA _ hx _).2 ⟨1, one_mem _, (one_mul _).symm⟩, rfl⟩

end PositivityTheory.Xgn.A_pull_line
end

