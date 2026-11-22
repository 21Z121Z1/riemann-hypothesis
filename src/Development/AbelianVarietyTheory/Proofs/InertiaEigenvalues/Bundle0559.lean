import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0460
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0294
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0543
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableAndCoverPrismHomOfPushout
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.BSP.CoverBC

variable {l : ℕ} {R : Type} [CommRing R]

theorem hom_ext {P P' : Obj l R} {a b : Hom P P'} (h : a.f = b.f) : a = b := by
  cases a; cases b; cases h; rfl

theorem comp_assoc {P₁ P₂ P₃ P₄ : Obj l R} (c : Hom P₃ P₄) (b : Hom P₂ P₃) (a : Hom P₁ P₂) :
    (c.comp b).comp a = c.comp (b.comp a) := hom_ext rfl

theorem qmap_comp {P₁ P₂ P₃ : Obj l R} (g : Hom P₂ P₃) (f : Hom P₁ P₂) (m : ℕ) :
    qmap (g.comp f) m = (qmap g m).comp (qmap f m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem of_isPushout {P : ∀ {A B : Type} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hP : RingHom.IsStableUnderBaseChange @P)
    {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    {φ : A →+* B} {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'}
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (h : P φ) : P φ' := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  exact hP A B A' B' h

end GlobalTheory.BSP.CoverBC

namespace GlobalTheory.BSP.CoverBC

variable {l : ℕ} {R : Type} [CommRing R]

theorem flat_of_isPO {B C B' C' : Obj l R} {h : Hom B C} {k : Hom B B'} {k' : Hom C C'} {h' : Hom B' C'}
    (H : IsPO h k k' h') (hf : ∀ m : ℕ, (qmap h m).Flat) (m : ℕ) : (qmap h' m).Flat :=
  of_isPushout RingHom.Flat.isStableUnderBaseChange (H.po m) (hf m)

theorem faithfullyFlat_of_isPO {B C B' C' : Obj l R} {h : Hom B C} {k : Hom B B'} {k' : Hom C C'}
    {h' : Hom B' C'} (H : IsPO h k k' h') (hf : ∀ m : ℕ, (qmap h m).FaithfullyFlat) (m : ℕ) :
    (qmap h' m).FaithfullyFlat :=
  of_isPushout RingHom.FaithfullyFlat.isStableUnderBaseChange (H.po m) (hf m)

end GlobalTheory.BSP.CoverBC

open GlobalTheory.BSP.CoverBC in

theorem GlobalTheory.BSP.stable_cover_of_isPO : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C B' C' : Obj l R)
    (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C'),
    IsPO h k k' h' → (Stable h → Stable h') ∧ (Cover h → Cover h') := by
  intro l _ R _ B C B' C' h k k' h' H
  have st : Stable h → Stable h' := by
    intro hs
    refine ⟨flat_of_isPO H hs.flat, fun B'' k₂ => ?_⟩
    obtain ⟨C'', k₀, h'', H₂⟩ := hs.po B'' (k₂.comp k)
    have e : k₀.comp h = (h''.comp k₂).comp k := by rw [H₂.comm, comp_assoc]
    obtain ⟨c, ⟨hc₁, hc₂⟩, -⟩ := GlobalTheory.T.prismPushoutModAdicPow_universal l R B C B' C' h k k' h' H C'' k₀ (h''.comp k₂) e
    refine ⟨C'', c, h'', ⟨hc₂, fun m => ?_⟩⟩
    have s := H₂.po m
    rw [← hc₁, qmap_comp, qmap_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp] at s
    refine IsPushout.of_top s ?_ (H.po m)
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← qmap_comp, ← qmap_comp, hc₂]
  exact ⟨st, fun hc => ⟨st hc.stable, faithfullyFlat_of_isPO H hc.ff⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleDescentFiniteLevel
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LevH

open CategoryTheory

theorem lev_ring {A B D T : Type} [CommRing A] [CommRing B] [CommRing D] [CommRing T] [Algebra A B]
    (p q : B →+* D) (q₁₂ q₂₃ q₁₃ : D →+* T) (q₃ : B →+* T)
    (hff : (algebraMap A B).FaithfullyFlat)
    (hpo1 : IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom p) (CommRingCat.ofHom q))
    (hpo2 : IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (p.comp (algebraMap A B)))
      (CommRingCat.ofHom q₃) (CommRingCat.ofHom q₁₂))
    (e1 : q₂₃.comp p = q₁₂.comp q) (e2 : q₂₃.comp q = q₃) (e3 : q₁₃.comp p = q₁₂.comp p) (e4 : q₁₃.comp q = q₃)
    (d : ℕ) (ε : Matrix (Fin d) (Fin d) D) (hε : IsUnit ε) (hc : ε.map q₁₂ * ε.map q₂₃ = ε.map q₁₃) :
    ∃ N : Submodule A (Fin d → B), (∀ z, z ∈ N ↔ (fun i => p (z i)) = ε.mulVec fun i => q (z i)) ∧
      Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  have hw : p.comp (algebraMap A B) = q.comp (algebraMap A B) := by
    have := congrArg CommRingCat.Hom.hom hpo1.w
    simpa using this
  have hr : ∀ c, p (algebraMap A B c) = q (algebraMap A B c) := fun c => RingHom.congr_fun hw c
  let N : Submodule A (Fin d → B) :=
    { carrier := {z | (fun i => p (z i)) = ε.mulVec fun i => q (z i)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have e : (fun i => q ((a + b) i)) = (fun i => q (a i)) + fun i => q (b i) := by
          funext i; simp [map_add]
        rw [e, Matrix.mulVec_add, ← ha, ← hb]
        funext i; simp [map_add]
      zero_mem' := by
        simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
        exact (Matrix.mulVec_zero ε).symm
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq] at hz ⊢
        have e1 : (fun i => p ((c • z) i)) = q (algebraMap A B c) • fun i => p (z i) := by
          funext i; simp [Algebra.smul_def, map_mul, hr]
        have e2 : (fun i => q ((c • z) i)) = q (algebraMap A B c) • fun i => q (z i) := by
          funext i; simp [Algebra.smul_def, map_mul]
        rw [e1, e2, Matrix.mulVec_smul, hz] }
  exact ⟨N, fun z => Iff.rfl, GlobalTheory.T.descent_free_module_cocycle A B D T p q q₁₂ q₂₃ q₁₃ q₃ hff hpo1 hpo2 e1 e2 e3 e4 d ε hε hc N
    fun z => Iff.rfl⟩

variable {l : ℕ} {R : Type} [CommRing R]

theorem hom_comp_assoc {B C D E : Obj l R} (h : Hom D E) (g : Hom C D) (f : Hom B C) :
    (h.comp g).comp f = h.comp (g.comp f) := Hom.ext' rfl

theorem lev_prism [Fact l.Prime] {B C D : Obj l R} (h : Hom B C) (p q : Hom C D) (hc : Cover h) (hpo : IsPO h h p q)
    (m : ℕ) (d : ℕ) (ε : Matrix (Fin d) (Fin d) D.A) (hε : IsUnit ε)
    (hcoc : ∀ (T : Obj l R) (q₁₂ q₂₃ q₁₃ : Hom D T) (q₃ : Hom C T), q₂₃.comp p = q₁₂.comp q → q₂₃.comp q = q₃ →
      q₁₃.comp p = q₁₂.comp p → q₁₃.comp q = q₃ → ε.map q₁₂.f * ε.map q₂₃.f = ε.map q₁₃.f) :
    letI := (qmap h m).toAlgebra
    ∃ N : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m),
      (∀ z, z ∈ N ↔ (fun i => qmap p m (z i)) = (ε.map (Ideal.Quotient.mk (adI D ^ m))).mulVec
        fun i => qmap q m (z i)) ∧
      Module.Finite (B.A ⧸ adI B ^ m) ↥N ∧ Module.Projective (B.A ⧸ adI B ^ m) ↥N ∧
        IsBaseChange (C.A ⧸ adI C ^ m) N.subtype := by
  letI := (qmap h m).toAlgebra
  have c1 : p.comp h = q.comp h := hpo.comm
  refine Exists.elim (hc.stable.po D (p.comp h)) fun T hT => Exists.elim hT fun q₃ hT => Exists.elim hT
    fun q₁₂ hT => ?_
  have c2 : q₃.comp h = q₁₂.comp (p.comp h) := hT.comm
  refine Exists.elim (GlobalTheory.T.prismPushoutModAdicPow_universal l R B C C D h h p q hpo T (q₁₂.comp q) q₃ (by
      rw [hom_comp_assoc, ← c1, c2])) fun q₂₃ h23 => ?_
  refine Exists.elim (GlobalTheory.T.prismPushoutModAdicPow_universal l R B C C D h h p q hpo T (q₁₂.comp p) q₃ (by
      rw [hom_comp_assoc, c2])) fun q₁₃ h13 => ?_
  have hpo2 := hT.po m
  have hq : qmap (p.comp h) m = (qmap p m).comp (qmap h m) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  rw [hq] at hpo2
  have hq2 : ∀ (k k' : Hom D T) (k'' : Hom C T), k.comp p = k'.comp q → (qmap k m).comp (qmap p m) = (qmap k' m).comp (qmap q m) :=
    fun k k' k'' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  have hq3 : ∀ (k : Hom D T) (k' : Hom C T), k.comp q = k' → (qmap k m).comp (qmap q m) = qmap k' m :=
    fun k k' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  have hq4 : ∀ (k : Hom D T) (k' : Hom D T), k.comp p = k'.comp p → (qmap k m).comp (qmap p m) = (qmap k' m).comp (qmap p m) :=
    fun k k' e => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg (fun H : Hom C T => Ideal.Quotient.mk (adI T ^ m) (H.f x)) e)
  refine lev_ring (qmap p m) (qmap q m) (qmap q₁₂ m) (qmap q₂₃ m) (qmap q₁₃ m) (qmap q₃ m) (hc.ff m) (hpo.po m) hpo2
    (hq2 q₂₃ q₁₂ q₃ h23.1.1) (hq3 q₂₃ q₃ h23.1.2) (hq4 q₁₃ q₁₂ h13.1.1) (hq3 q₁₃ q₃ h13.1.2) d _
    (hε.map (Ideal.Quotient.mk (adI D ^ m)).mapMatrix) ?_
  have := congrArg (fun M : Matrix (Fin d) (Fin d) T.A => M.map (Ideal.Quotient.mk (adI T ^ m)))
    (hcoc T q₁₂ q₂₃ q₁₃ q₃ h23.1.1 h23.1.2 h13.1.1 h13.1.2)
  simp only [Matrix.map_mul] at this
  exact this

end GlobalTheory.BSP.LevH

namespace GlobalTheory.BSP.LevH

theorem descent_at_level : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ m : ℕ, letI := (qmap h m).toAlgebra; ∃ N : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m), (∀ z, z ∈ N ↔ (fun i => qmap p m (z i)) = ((S.ε (p.comp f) (q.comp f)).map (Ideal.Quotient.mk (adI D ^ m))).mulVec fun i => qmap q m (z i)) ∧ Module.Finite (B.A ⧸ adI B ^ m) ↥N ∧ Module.Projective (B.A ⧸ adI B ^ m) ↥N ∧ IsBaseChange (C.A ⧸ adI C ^ m) N.subtype := by
  intro l _ K bk d S B C D h f p q hc hpo m
  refine lev_prism h p q hc hpo m d (S.ε (p.comp f) (q.comp f))
    ⟨⟨S.ε (p.comp f) (q.comp f), S.ε (q.comp f) (p.comp f), by rw [S.ε_trans, S.ε_refl],
      by rw [S.ε_trans, S.ε_refl]⟩, rfl⟩ ?_
  intro T q₁₂ q₂₃ q₁₃ q₃ e1 e2 e3 e4
  have a1 : q₂₃.comp (p.comp f) = q₁₂.comp (q.comp f) := by rw [← hom_comp_assoc, e1, hom_comp_assoc]
  have a2 : q₂₃.comp (q.comp f) = q₃.comp f := by rw [← hom_comp_assoc, e2]
  have a3 : q₁₃.comp (p.comp f) = q₁₂.comp (p.comp f) := by rw [← hom_comp_assoc, e3, hom_comp_assoc]
  have a4 : q₁₃.comp (q.comp f) = q₃.comp f := by rw [← hom_comp_assoc, e4]
  rw [S.ε_nat, S.ε_nat, S.ε_nat, a1, a2, a3, a4, S.ε_trans]

end GlobalTheory.BSP.LevH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateCharacterFiniteOnInertiaOfEigenvector
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.TateEigen

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_pos : 0 < ‖((l : ℕ) : ℤ_[l])‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem norm_l_lt_one : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
  rw [PadicInt.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem exists_pow_near_one (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ u : ℤ_[l]ˣ, ‖((u ^ N : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ k := by
  have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨Nat.card (ZMod (l ^ k))ˣ, Nat.card_pos, fun u => ?_⟩
  have h : (Units.map (PadicInt.toZModPow (p := l) k).toMonoidHom u) ^ Nat.card (ZMod (l ^ k))ˣ = 1 :=
    pow_card_eq_one'
  have h2 : ((u ^ Nat.card (ZMod (l ^ k))ˣ : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈
      RingHom.ker (PadicInt.toZModPow (p := l) k) := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    rw [← map_pow] at h
    exact congrArg Units.val h
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨w, hw⟩ := h2
  rw [hw, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one w)

theorem exists_norm_eq_pow (x : ℤ_[l]) (hx : x ≠ 0) : ∃ k : ℕ, ‖x‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k := by
  refine ⟨x.valuation, ?_⟩
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [norm_mul, PadicInt.norm_units, one_mul, norm_pow]

theorem finite_on_inertia : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (y : ℂ_[l]), y ≠ 0 →
    (∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y) →
    ∃ N : ℕ, 0 < N ∧ ∀ γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup, η γ ^ N = 1 := by
  intro l _ η y hy hη
  obtain ⟨c, hc, hax⟩ := GlobalTheory.T.axLemma_padicComplex_fixed_element_approximation l
  have hτ0 := norm_l_pos (l := l)
  have hτ1 := norm_l_lt_one (l := l)
  set τ := ‖((l : ℕ) : ℤ_[l])‖ with hτ
  obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hc) hτ1
  obtain ⟨N, hN, hNu⟩ := exists_pow_near_one (l := l) (k₁ + 2)
  refine ⟨N, hN, fun γ₀ hγ₀ => ?_⟩
  by_contra hne
  set γ := γ₀ ^ N with hγdef
  have hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := pow_mem hγ₀ N
  have hηγ : η γ = η γ₀ ^ N := map_pow _ _ _
  have hne' : (η γ : ℤ_[l]) - 1 ≠ 0 := by
    intro h
    apply hne
    rw [← hηγ]
    exact Units.ext (sub_eq_zero.1 h)
  obtain ⟨k, hk⟩ := exists_norm_eq_pow _ hne'
  have hkk : k₁ + 2 ≤ k := by
    have := hNu (η γ₀)
    rw [← hηγ, hk] at this
    exact (pow_le_pow_iff_right_of_lt_one₀ hτ0 hτ1).1 this
  have hk2 : 2 ≤ k := by omega
  obtain ⟨H, hmem, hnorm, hidx, hidx', hpow, hgen⟩ := GlobalTheory.T.exists_normal_subgroup_filtration_index_bounded l η γ k hk2 hk
  obtain ⟨ρ, hρ0, hρ1, hgain⟩ := GlobalTheory.T.norm_inertia_partialTrace_geometric_le l γ hγ H k hnorm hidx hidx' hpow hgen
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hc) hρ1
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hr : 0 < τ ^ (k + n) * ‖y‖ := by positivity
  obtain ⟨z, hz, hyz⟩ := hax (H n) y (τ ^ (k + n) * ‖y‖) hr (by
    intro g hg
    have e : Per.σC g y - y = algebraMap ℚ_[l] ℂ_[l] ((((η g : ℤ_[l]) - 1 : ℤ_[l])) : ℚ_[l]) * y := by
      rw [hη g, PadicInt.coe_sub, PadicInt.coe_one, map_sub, map_one]; ring
    rw [e, norm_mul, norm_algebraMap']
    exact mul_le_mul_of_nonneg_right ((hmem n g).1 hg) hy0.le)
  have hv : ∀ g ∈ H n, g (γ z - algebraMap ℚ_[l] (Om l) ((η γ : ℤ_[l]) : ℚ_[l]) * z) =
      γ z - algebraMap ℚ_[l] (Om l) ((η γ : ℤ_[l]) : ℚ_[l]) * z := by
    intro g hg
    have h1 := hz _ ((hnorm n).conj_mem' g hg γ)
    have h2 : g (γ z) = γ z := by
      have := congrArg γ h1
      simpa [mul_assoc] using this
    rw [map_sub, map_mul, h2, hz g hg, AlgEquiv.commutes]
  have hest := GlobalTheory.T.tate_estimate_galois_eigenvector_cLTate l γ ((η γ : ℤ_[l]) : ℚ_[l]) y z (l ^ n) (c * (τ ^ (k + n) * ‖y‖)) (ρ ^ n)
    (hη γ) (PadicInt.norm_units (η γ)) (hz _ (hpow n)) hyz (hgain n _ hv) (by positivity)
  have hlte := GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one l (η γ : ℤ_[l]) k hk2 hk n
  have e1 : ‖((η γ : ℤ_[l]) : ℚ_[l]) ^ l ^ n - 1‖ = τ ^ (k + n) := by
    rw [hτ, ← hlte, PadicInt.norm_def]; push_cast; rfl
  have e2 : ‖((η γ : ℤ_[l]) : ℚ_[l]) - 1‖ = τ ^ k := by
    rw [hτ, ← hk, PadicInt.norm_def]; push_cast; rfl
  rw [e1, e2] at hest
  have hk' : τ ^ k < c⁻¹ := lt_of_le_of_lt (pow_le_pow_of_le_one hτ0.le hτ1.le (by omega)) hk₁
  have key : ∀ a : ℝ, a < c⁻¹ → a * (c * (τ ^ (k + n) * ‖y‖)) < τ ^ (k + n) * ‖y‖ := by
    intro a ha
    have : a * c < 1 := by
      have := mul_lt_mul_of_pos_right ha hc
      rwa [inv_mul_cancel₀ hc.ne'] at this
    rw [← mul_assoc]
    exact mul_lt_of_lt_one_left hr this
  exact absurd hest (not_le.2 (max_lt (key _ hk') (key _ hn)))

end GlobalTheory.TateEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorFormulaPiInvPrimeModEisensteinPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

section Scal

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem galOD_crisToOD (g : GQ l) (x : OCr l O) :
    galOD O g (crisToOD l O x) = crisToOD l O (galOCr O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.BdRp l => o ⊗ₜ[ℤ_[l]] y)
      ((GlobalTheory.MemLoc.crisP_unique_equivariant l (crisP l) (isCrisP_crisP l)).2.1 g w).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isUnit_natCast_OD {n : ℕ} (hn : n ≠ 0) : IsUnit (n : OD l O) := by
  have h0 : ((n : ℕ) : ℤ_[l]) ≠ 0 := by exact_mod_cast hn
  have h1 := congrArg (algebraMap ℤ_[l] (OD l O)) (PadicInt.unitCoeff_spec h0)
  rw [map_natCast, map_mul, map_pow, map_natCast] at h1
  rw [h1]
  exact ((PadicInt.unitCoeff h0).isUnit.map _).mul (isUnit_l_OD.pow _)

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

variable (O K) in

theorem dvd_toOD_mu (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) :
    ϖ.iAl O K (EIn l e _) ∣ toOD l O (1 ⊗ₜ ϖ.mu g) := by
  have hξ : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) :=
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))
  have hmem : ϖ.mu g ∈ Ideal.span {ϖ.ev 1 (eis l 1 e)} := by
    rw [ϖ.span_ev_eis 1]
    exact ϖ.theta_mu (ϖ.gal_pi a g)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨1 ⊗ₜ ainfToBdRp l c, ?_⟩
  rw [hξ, ← hc]
  change (1 : O) ⊗ₜ[ℤ_[l]] ainfToBdRp l (c * _) = _
  rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]

variable (O) in

theorem crisToOD_muDiv (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (i : ℕ) :
    crisToOD l O (ϖ.muDiv a O g i) = toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) := by
  have h1 := congrArg (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O)
    (factorial_mul_dpow (ϖ.mu g) (ϖ.theta_mu (ϖ.gal_pi a g)) i)
  rw [map_mul, map_natCast, map_pow] at h1
  have h2 := congrArg (crisToOD l O) h1
  rw [map_mul, map_natCast, map_pow, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeRight_apply, ← toOCr_tmul, crisToOD_toOCr] at h2
  have hu := isUnit_natCast_OD (l := l) (O := O) i.factorial_ne_zero
  rw [← h2, mul_comm, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  rfl

variable (K) in

theorem taylor_S_mod (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (s : S O K e) (R : ℕ) :
    ϖ.iAl O K (EIn l e _) ^ R ∣ galOD O g (crisToOD l O (ϖ.iS O K s)) -
      ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
  obtain ⟨N, hN⟩ := GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ R
  refine GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ R _ fun k => ?_
  obtain ⟨M₀, hM₀⟩ := ϖ.taylor_S a O K g s (N + k)
  obtain ⟨z, hz⟩ := hM₀ (max M₀ R) (le_max_left _ _)
  obtain ⟨y, hy⟩ := hN z
  refine ⟨y, ?_⟩
  have hz' := congrArg (crisToOD l O) hz
  simp only [map_sub, map_sum, map_mul, map_pow, map_natCast, crisToOD_muDiv] at hz'
  rw [← galOD_crisToOD, ← Finset.sum_range_add_sum_Ico _ (le_max_right M₀ R)] at hz'
  have key : galOD O g (crisToOD l O (ϖ.iS O K s)) -
      ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) - (l : OD l O) ^ k * toOD l O y =
      (l : OD l O) ^ k * ((l : OD l O) ^ N * crisToOD l O z - toOD l O y) +
        ∑ i ∈ Finset.Ico R (max M₀ R), toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
    linear_combination hz'
  rw [key]
  refine dvd_add (Dvd.dvd.mul_left hy _) (Finset.dvd_sum fun i hi => ?_)
  have hi' : R ≤ i := (Finset.mem_Ico.1 hi).1
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ((pow_dvd_pow _ hi').trans
    (pow_dvd_pow_of_dvd (dvd_toOD_mu O K ϖ g) i)) _) _

end Scal

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep

section Scal2

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [TameDescentExponentData K l e a] [CompleteSpace K]

theorem taylor_invL_mod (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) {f : K⟦X⟧}
    (hf : f ∈ invL l (S O K e)) (R : ℕ) :
    galOD O g (ϖ.iHat O K (hatR O f)) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i *
      Ring.inverse (i.factorial : OD l O) * ϖ.iHat O K (hatR O (descN K i f)) ∈
      Ideal.span {ϖ.iAl O K (EIn l e _) ^ R} := by
  have hiHat : ∀ (f' : K⟦X⟧) (hf' : f' ∈ invL l (S O K e)), ϖ.iHat O K (hatR O f') = ϖ.iSD O K ⟨f', hf'⟩ :=
    fun f' hf' => (GlobalTheory.BKReal.TwoMaps.iSD_eq_iHat_of_hat l a e O K t ϖ ⟨f', hf'⟩ (hatR O f') (by
      rw [hatR_of_mem (O := O) (invL_S_le_Rpi l e hf')]
      exact hat_coe_Rpi l e ⟨f', invL_S_le_Rpi l e hf'⟩)).symm
  obtain ⟨n, hn⟩ := hf
  have hC : ((l : S O K e) : K⟦X⟧) ^ n = C ((l : K) ^ n) := by simp
  have hlin : ∀ (i : ℕ) (x : K⟦X⟧), ((l : S O K e) : K⟦X⟧) ^ n * descN K i x =
      descN K i (((l : S O K e) : K⟦X⟧) ^ n * x) := fun i x => by
    rw [hC, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  have hdesc : ∀ i : ℕ, descN K i f ∈ invL l (S O K e) := fun i =>
    ⟨n, by rw [hlin]; exact descN_mem_S e i hn⟩
  set s : S O K e := ⟨_, hn⟩ with hs
  have e0 : (l : OD l O) ^ n * ϖ.iSD O K ⟨f, ⟨n, hn⟩⟩ = crisToOD l O (ϖ.iS O K s) := by
    have h1 : (l : invL l (S O K e)) ^ n * ⟨f, ⟨n, hn⟩⟩ = algebraMap (S O K e) (invL l (S O K e)) s :=
      Subtype.ext (by simp [s])
    have h2 := congrArg (ϖ.iSD O K) h1
    rw [map_mul, map_pow, map_natCast] at h2
    rw [h2]
    exact ϖ.iSD_of_mem O K s.2 _
  have ei : ∀ i : ℕ, (l : OD l O) ^ n * ϖ.iSD O K ⟨descN K i f, hdesc i⟩ =
      crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := fun i => by
    have h1 : (l : invL l (S O K e)) ^ n * ⟨descN K i f, hdesc i⟩ =
        algebraMap (S O K e) (invL l (S O K e)) ⟨descN K i s, descN_mem_S e i s.2⟩ :=
      Subtype.ext (by
        change ((l : K⟦X⟧)) ^ n * descN K i f = descN K i (((l : S O K e) : K⟦X⟧) ^ n * f)
        rw [← hlin]
        simp)
    have h2 := congrArg (ϖ.iSD O K) h1
    rw [map_mul, map_pow, map_natCast] at h2
    rw [h2]
    exact ϖ.iSD_of_mem O K (descN_mem_S e i s.2) _
  have g0 := congrArg (galOD O g) e0
  rw [map_mul, map_pow, map_natCast] at g0
  have key : (l : OD l O) ^ n * (galOD O g (ϖ.iHat O K (hatR O f)) - ∑ i ∈ Finset.range R,
      toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iHat O K (hatR O (descN K i f))) =
      galOD O g (crisToOD l O (ϖ.iS O K s)) -
        ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
    rw [hiHat f ⟨n, hn⟩, ← g0, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hiHat _ (hdesc i), ← ei i]
    ring
  have hW := Ideal.mem_span_singleton.2 (taylor_S_mod K ϖ g s R)
  rw [← key] at hW
  exact (Ideal.unit_mul_mem_iff_mem _ (isUnit_l_OD.pow n)).1 hW

theorem galOD_idem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (τ : ZMod a) :
    galOD O g (idem (constD t) τ) = idem (constD t) τ := by
  have h : ∀ x ∈ Kunr l a, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (ϖ.Kunr_le_field a hx)
  change galOD O g (toOD l O (constA t _)) = toOD l O (constA t _)
  rw [← crisToOD_toOCr, galOD_crisToOD, galOCr_toOCr, galOA_constA t h]

end Scal2

theorem taylor_iD_mod_ED : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ invL l (S O K e)) → ∀ R : ℕ, GlobalTheory.GalStep.galOD O g (ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (f τ))) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (descN K i (f τ))) ∈ Ideal.span {GlobalTheory.GalStep.ED K t ϖ ^ R} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ g hg f hf R
  let g' : ↥(GK (ϖ.field a)) := ⟨g, hg⟩
  have hED : ED K t ϖ = ϖ.iAl O K (EIn l e _) := (glue_const _ _ _).trans (ϖ.iHat_ofAl O K _)
  rw [hED]
  have hfix : ∀ τ, galOD O g (idem (constD t) τ) = idem (constD t) τ := galOD_idem t ϖ g'
  have hsplit : galOD O g (ϖ.iD t K (fun τ => hatR O (f τ))) - ∑ i ∈ Finset.range R,
      toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        ϖ.iD t K (fun τ => hatR O (descN K i (f τ))) =
      ∑ τ, idem (constD t) τ * (galOD O g (ϖ.iHat O K (hatR O (f τ))) - ∑ i ∈ Finset.range R,
        toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          ϖ.iHat O K (hatR O (descN K i (f τ)))) := by
    simp only [PiSys.iD, glue_apply, map_sum, map_mul, hfix, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit]
  exact Ideal.sum_mem _ fun τ _ => Ideal.mul_mem_left _ _ (taylor_invL_mod t ϖ g' (hf τ) R)

end GlobalTheory.GalStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantMemReductionOfFrobeniusEquationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_invariant_mem_reduction_of_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x : κ → Cb l), (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, autCb l (galTilt l (g : GQ l)) (x j) = x j) → (∀ (T : Type) [CommRing T] (i₁ i₂ : Cb l →+* T), (∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), i₁ y = i₂ y) → ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) → ∀ j, x j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  first | exact @GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant | exact GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant | (intros; apply GlobalTheory.BSP.TwoCopy.mem_reduction_of_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformizerFamilyFrobeniusCongrPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizerFamily_frobenius_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → uFam a K ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.uFam_mem_GoodSet | exact GlobalTheory.CrysPrism.uFam_mem_GoodSet | (intros; apply GlobalTheory.CrysPrism.uFam_mem_GoodSet <;> assumption)
end

