import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0040
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0007

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsWeightOfIntertwine
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgIso

open CompanionTheory.RgExh
open Formalism.REAL (GlRel qdet qminor Tm KHighest IsWeight)
open CompanionTheory.D.LK (LocFin IsMin)
open CompanionTheory.D.DSIC (KStab)

variable {n : ℕ}

theorem iso_refl (X : GMod n) : Iso X X := by
  exact ⟨LinearEquiv.refl ℂ X.V, fun a b x => rfl⟩

theorem intertwine_symm {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x))
    (a b : Fin n) (y : Y.V) : e.symm (Y.E a b y) = X.E a b (e.symm y) := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

theorem iso_symm {X Y : GMod n} : Iso X Y → Iso Y X := by
  rintro ⟨e, he⟩
  exact ⟨e.symm, intertwine_symm e he⟩

theorem iso_trans {X Y Z : GMod n} : Iso X Y → Iso Y Z → Iso X Z := by
  rintro ⟨e, he⟩ ⟨f, hf⟩
  exact ⟨e.trans f, fun a b x => by rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he, hf]⟩

def cj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.End ℂ V →+* Module.End ℂ W where
  toFun f := e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' f g := by ext; simp
  map_zero' := by ext; simp
  map_add' f g := by ext; simp

theorem cj_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (f : Module.End ℂ V) (w : W) : cj e f w = e (f (e.symm w)) := rfl

theorem cj_smul_one {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (c : ℂ) : cj e (c • (1 : Module.End ℂ V)) = c • (1 : Module.End ℂ W) := by
  refine LinearMap.ext fun w => ?_
  rw [cj_apply]
  simp

theorem cj_algebraMap {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (c : ℂ) : cj e (algebraMap ℂ (Module.End ℂ V) c) = algebraMap ℂ (Module.End ℂ W) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, cj_smul_one]

theorem cj_E {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (a b : Fin n) :
    cj e (X.E a b) = Y.E a b := by
  refine LinearMap.ext fun w => ?_
  rw [cj_apply, he, LinearEquiv.apply_symm_apply]

theorem cj_Tm {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (u : ℂ)
    (a b : Fin n) : cj e (Tm X.E u a b) = Tm Y.E u a b := by
  unfold Formalism.REAL.Tm
  rw [map_add, cj_E e he]
  split_ifs
  · rw [cj_algebraMap]
  · rw [map_zero]

theorem cj_qdet {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (u : ℂ) :
    cj e (qdet X.E u) = qdet Y.E u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, cj_Tm e he]

theorem scalChar_of_iso {X Y : GMod n} (h : Iso X Y) (χ : Fin n → ℂ) (hX : ScalChar X χ) : ScalChar Y χ := by
  obtain ⟨e, he⟩ := h
  intro t
  rw [← cj_qdet e he, hX t, cj_smul_one]

theorem hasChar_of_iso {X Y : GMod n} (h : Iso X Y) (χ : Fin n → ℂ) (hX : HasChar X χ) : HasChar Y χ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨k, hk⟩ := hX
  refine ⟨k, fun t => ?_⟩
  rw [← cj_qdet e he, ← cj_smul_one e, ← map_sub, ← map_pow, hk t, map_zero]

theorem isSimple_of_iso {X Y : GMod n} (h : Iso X Y) (hX : IsSimple X) : IsSimple Y := by
  obtain ⟨e, he⟩ := h
  refine ⟨?_, fun S hS => ?_⟩
  · haveI := hX.1
    exact e.symm.toEquiv.nontrivial
  · have hS' : ∀ a b, ∀ x ∈ S.comap (e : X.V →ₗ[ℂ] Y.V), X.E a b x ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by
      intro a b x hx
      simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
      rw [he]
      exact hS a b _ hx
    rcases hX.2 _ hS' with h0 | h1
    · left
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_bot]
      have hy' : e.symm y ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by simpa using hy
      rw [h0, Submodule.mem_bot] at hy'
      simpa using hy'
    · right
      rw [eq_top_iff]
      intro y _
      have hy' : e.symm y ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by
        rw [h1]
        trivial
      simpa using hy'

theorem locFin_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (hX : LocFin ε X.E) : LocFin ε Y.E := by
  obtain ⟨e, he⟩ := h
  intro y
  obtain ⟨S, hfd, hst, hx⟩ := hX (e.symm y)
  refine ⟨S.map (e : X.V →ₗ[ℂ] Y.V), ?_, ?_, ?_⟩
  · haveI := hfd
    exact Module.Finite.map S _
  · intro a b hab v hv
    obtain ⟨x, hxS, rfl⟩ := Submodule.mem_map.mp hv
    have hm := Submodule.mem_map_of_mem (f := (e : X.V →ₗ[ℂ] Y.V)) (hst a b hab x hxS)
    simpa [he] using hm
  · exact ⟨e.symm y, hx, by simp⟩

theorem isWeight_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (he : ∀ a b x, e (E a b x) = F a b (e x)) {μ : Fin n → ℝ} {x : V} (h : IsWeight E μ x) :
    IsWeight F μ (e x) := by
  intro a
  rw [← he, h a, map_smul]

theorem kHighest_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (he : ∀ a b x, e (E a b x) = F a b (e x)) {μ : Fin n → ℝ} {x : V} (h : KHighest ε E μ x) :
    KHighest ε F μ (e x) := by
  exact ⟨isWeight_of_intertwine e E F he h.1, fun a b hab hε => by rw [← he, h.2 a b hab hε, map_zero]⟩

theorem intWt_of_iso {X Y : GMod n} (h : Iso X Y) (hX : IntWt X) : IntWt Y := by
  obtain ⟨e, he⟩ := h
  intro μ y hy hw
  have hx : e.symm y ≠ 0 := by simpa using hy
  exact hX μ (e.symm y) hx (isWeight_of_intertwine e.symm Y.E X.E (fun a b z => intertwine_symm e he a b z) hw)

theorem algDS_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ)
    (hX : AlgDS ε X s mu) : AlgDS ε Y s mu := by
  obtain ⟨e, he⟩ := h
  obtain ⟨h1, h2, h3, v, hv, hk⟩ := hX
  refine ⟨h1, h2, ?_, e v, by simpa using hv,
    kHighest_of_intertwine e _ (fun a b => X.E (s a) (s b)) (fun a b => Y.E (s a) (s b))
      (fun a b x => he (s a) (s b) x) hk⟩
  intro μ y hy hky
  exact h3 μ (e.symm y) (by simpa using hy)
    (kHighest_of_intertwine e.symm _ (fun a b => Y.E (s a) (s b)) (fun a b => X.E (s a) (s b))
      (fun a b z => intertwine_symm e he (s a) (s b) z) hky)

theorem coneDS_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ)
    (hX : CompanionTheory.RgExh.Fin.ConeDS ε X s mu) : CompanionTheory.RgExh.Fin.ConeDS ε Y s mu := by
  obtain ⟨e, he⟩ := h
  intro ν y hy hky
  exact hX ν (e.symm y) (by simpa using hy)
    (kHighest_of_intertwine e.symm _ (fun a b => Y.E (s a) (s b)) (fun a b => X.E (s a) (s b))
      (fun a b z => intertwine_symm e he (s a) (s b) z) hky)

theorem isoFacts : CompanionTheory.RgExh.Fin.IsoFacts := by
  intro n ε X Y Z
  exact ⟨iso_refl X, iso_symm, iso_trans, fun h => ⟨isSimple_of_iso h, isSimple_of_iso (iso_symm h)⟩,
    fun h χ => ⟨scalChar_of_iso h χ, scalChar_of_iso (iso_symm h) χ⟩,
    fun h χ => ⟨hasChar_of_iso h χ, hasChar_of_iso (iso_symm h) χ⟩,
    fun h => ⟨locFin_of_iso ε h, locFin_of_iso ε (iso_symm h)⟩,
    fun h => ⟨intWt_of_iso h, intWt_of_iso (iso_symm h)⟩,
    fun h s mu => ⟨algDS_of_iso ε h s mu, algDS_of_iso ε (iso_symm h) s mu⟩,
    fun h s mu => ⟨coneDS_of_iso ε h s mu, coneDS_of_iso ε (iso_symm h) s mu⟩⟩

end GlobalTheory.CompanionTheory.RgIso
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestOfPerm
section
noncomputable section

namespace GlobalTheory.CompanionTheory.DSData

open Formalism.REAL (KHighest)
open CompanionTheory.RgExh CompanionTheory.RgExh.Fin

variable {n : ℕ}

theorem kHighest_of_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x) :
    KHighest ε E (μ ∘ s.symm) x := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · simpa using h.1 (s.symm a)
  · have h1 : (ε ∘ s) (s.symm a) = (ε ∘ s) (s.symm b) := by simpa using he
    simpa using h.2 (s.symm a) (s.symm b) (GlobalTheory.DSId.PermK.mono_symm hs a b hab h1) h1

theorem kHighest_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest ε E (μ ∘ s.symm) x) :
    KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x := by
  refine ⟨fun a => ?_, fun a b hab he => h.2 _ _ (hs a b hab he) he⟩
  simpa using h.1 (s a)

theorem dsOfData : DSOfData := by
  intro n ε H _ _ σ D E hK s mu hSq hA
  obtain ⟨-, hord, hmin, v, hv0, hv⟩ := hA
  obtain ⟨hT, -, -, hS, -⟩ := GlobalTheory.DSId.PermK.permKType n ε s H σ hord
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.1 hSq
  have e : ∀ f : Fin n → ℝ, (f ∘ s.symm) ∘ s = f := fun f => by funext a; simp
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · obtain ⟨T, hT'⟩ := hK.ty _ v hv0 (kHighest_of_perm hord hv)
    refine ⟨T, ?_⟩
    have h6 := (hT _ T).1 hT'
    rwa [e] at h6
  · intro μ S hS'
    have h6 : Formalism.MainNotions.S.IsKTypeOf ε σ (μ ∘ s.symm) S := by
      refine (hT _ S).2 ?_
      rwa [e]
    obtain ⟨w, hw0, -, hw⟩ := hK.hw _ S h6
    exact hmin μ w hw0 (kHighest_perm hord hw)

end GlobalTheory.CompanionTheory.DSData
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestRenumber
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.LowestData

open Formalism.REAL (KHighest)
open GlobalTheory.LowestKTypeDetermines (rhoC_perm lowK_add strictAnti_add_rho nsq_add_cone eq_zero_of_nsq nsq_comp)

variable {n : ℕ}

theorem kHighest_renumber {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) {s s' : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b)
    (hs' : ∀ a b, a < b → ε (s' a) = ε (s' b) → s' a < s' b) {Λ : Fin n → ℝ} {v : V}
    (h : KHighest (ε ∘ s') (fun a b => E (s' a) (s' b)) Λ v) :
    KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (Λ ∘ s'.symm ∘ s) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · have := h1 (s'.symm (s a))
    simpa using this
  · have hlt := hs a b hab he
    have key : s'.symm (s a) < s'.symm (s b) := by
      by_contra hn
      have hle := not_lt.1 hn
      rcases hle.lt_or_eq with hl | he'
      · have := hs' _ _ hl (by simpa using he.symm)
        simp only [Equiv.apply_symm_apply] at this
        exact absurd this (not_lt.2 hlt.le)
      · have := s'.symm.injective he'
        exact absurd this hlt.ne'
    have := h2 _ _ key (by simpa using he)
    simpa using this

theorem dataUniq : CompanionTheory.RgExh.Fin.DataUniq := by
  intro n ε X s s' mu mu' h hc h'
  obtain ⟨hl, hs, -, v, hv0, hv⟩ := h
  obtain ⟨hl', hs', hmin', v', hv0', hv'⟩ := h'
  have add : ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ),
      PI.UpqRep.lowK ε lam + (2 : ℝ) • Formalism.REAL.rhoC ε = lam + Formalism.QuantumDeterminants.rhoStd n := fun ε lam => lowK_add ε lam
  have k1 := kHighest_renumber ε X.E hs hs' hv'
  have k2 := kHighest_renumber ε X.E hs' hs hv
  obtain ⟨c, hc1, e⟩ := hc _ v' hv0' k1
  have m2 := hmin' _ v hv0 k2
  set x := mu + Formalism.QuantumDeterminants.rhoStd n with hx
  set x' := mu' + Formalism.QuantumDeterminants.rhoStd n with hx'
  set Q : Fin n → ℝ := ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b with hQ
  have hsx : StrictAnti x := strictAnti_add_rho hl.1
  have hsx' : StrictAnti x' := strictAnti_add_rho hl'.1
  have r1 : x' ∘ s'.symm ∘ s = x + Q := by
    have e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s) := (add _ _).symm
    have e2 : x' = PI.UpqRep.lowK (ε ∘ s') mu' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s') := (add _ _).symm
    funext a
    have ea := congrFun e a
    rw [e1, e2, rhoC_perm s hs, rhoC_perm s' hs']
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, Equiv.apply_symm_apply] at ea ⊢
    rw [ea]; ring
  have r2 : x ∘ s.symm ∘ s' =
      PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s') := by
    have e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s) := (add _ _).symm
    rw [e1, rhoC_perm s hs, rhoC_perm s' hs']
    funext a
    simp
  have m3 : Formalism.REAL.nsq x' ≤ Formalism.REAL.nsq x := by
    have a1 : Formalism.REAL.nsq x' =
        PI.UpqRep.vNormSq (ε ∘ s') (PI.UpqRep.lowK (ε ∘ s') mu') := by
      rw [hx', ← add]; rfl
    have a2 : Formalism.REAL.nsq x = PI.UpqRep.vNormSq (ε ∘ s')
        (PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s') := by
      have := nsq_comp (s.symm * s') x
      have e3 : x ∘ ⇑(s.symm * s') = x ∘ s.symm ∘ s' := rfl
      rw [e3, r2] at this
      rw [← this]; rfl
    rw [a1, a2]; exact m2
  have m4 : Formalism.REAL.nsq (x + Q) = Formalism.REAL.nsq x' := by
    rw [← r1]
    exact nsq_comp (s'.symm * s) x'
  have h4 := nsq_add_cone hsx.antitone hc1
  have hQ0 : Q = 0 := eq_zero_of_nsq (by linarith)
  rw [hQ0, add_zero] at r1
  have hm : StrictMono (s'.symm * s) := fun a b hab => by
    have h5 := hsx hab
    rw [← r1] at h5
    exact hsx'.lt_iff_gt.1 h5
  have h6 : s'.symm * s = 1 := by
    have := Subsingleton.elim (hm.orderIsoOfSurjective _ (s'.symm * s).surjective) (OrderIso.refl _)
    exact Equiv.ext fun a => DFunLike.congr_fun this a
  have h7 : s = s' := by
    refine Equiv.ext fun a => ?_
    have := congrArg (fun t : Equiv.Perm (Fin n) => s' (t a)) h6
    simpa using this
  subst h7
  refine ⟨rfl, ?_⟩
  have h8 : x' = x := by
    simpa using r1
  exact (add_right_cancel h8).symm

end GlobalTheory.CompanionTheory.LowestData
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PathEndEqAddNat
section
namespace GlobalTheory.CompanionTheory.RgPath

open CompanionTheory.RgExh

theorem pathEnd_eq_add_nat {n : ℕ} (ss : List (_root_.Fin n)) :
    ∀ χ : _root_.Fin n → ℂ, ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a := by
  induction ss with
  | nil =>
    intro χ
    exact ⟨0, by funext a; simp [pathEnd], by simp⟩
  | cons s ss ih =>
    intro χ
    obtain ⟨m', h, hm⟩ := ih (χ + Pi.single s 1)
    refine ⟨m' + Pi.single s 1, ?_, ?_⟩
    · rw [pathEnd, h]
      funext a
      by_cases e : a = s
      · subst e
        simp
        ring
      · simp [Pi.single_eq_of_ne e]
    · intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · simp
      · have := hm a ha
        simp only [Pi.add_apply]
        omega

theorem pathEndNat : CompanionTheory.RgExh.Fin.PathEndNat := fun _ χ ss => pathEnd_eq_add_nat ss χ

end GlobalTheory.CompanionTheory.RgPath
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleDistinct
section
namespace GlobalTheory.CompanionTheory.RgExhFin

open CompanionTheory.RgExh

private theorem simplePath_cons_iff {n : ℕ} (χ : Fin n → ℂ) (a : Fin n) (l : List (Fin n)) :
    SimplePath χ (a :: l) ↔ (∀ r, r ≠ a → χ r ≠ χ a) ∧ SimplePath (χ + Pi.single a 1) l :=
  Iff.rfl

theorem simplePath_ne {n : ℕ} (ss : List (Fin n)) :
    ∀ χ : Fin n → ℂ, SimplePath χ ss → ∀ r s, r ≠ s → (r ∈ ss ∨ s ∈ ss) → χ r ≠ χ s := by
  induction ss with
  | nil =>
    intro χ _ r s _ h
    simp at h
  | cons a l ih =>
    intro χ hp r s hrs hmem
    rw [simplePath_cons_iff] at hp
    obtain ⟨h1, h2⟩ := hp
    by_cases hra : r = a
    · subst hra
      exact (h1 s (Ne.symm hrs)).symm
    by_cases hsa : s = a
    · subst hsa
      exact h1 r hrs
    have hmem' : r ∈ l ∨ s ∈ l := by
      simp only [List.mem_cons] at hmem
      tauto
    have h3 := ih _ h2 r s hrs hmem'
    simpa [Pi.single_apply, hra, hsa] using h3

theorem simpleDistinct : CompanionTheory.RgExh.Fin.SimpleDistinct := by
  unfold CompanionTheory.RgExh.Fin.SimpleDistinct
  intro n χ ss hp hall r s hrs
  by_contra hne
  exact simplePath_ne ss χ hp r s hne (Or.inl (hall r)) hrs

end GlobalTheory.CompanionTheory.RgExhFin
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitarizableOfSeparatingSmoothL2Maps
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFin

open CompanionTheory.RgExh ReciprocityTheory.ChartRestriction.DS

theorem unitarizable_of_separating_smooth_l2_maps : CompanionTheory.RgExh.Fin.UnitarizableOfL2Embedding := by
  intro n ε X hL hS
  obtain ⟨hnt, hsub⟩ := hS
  obtain ⟨u, hu⟩ := exists_ne (0 : X.V)
  obtain ⟨c, hc, hcu⟩ := hL u hu
  have h0 : c ≠ 0 := fun h => hcu (by simp [h])
  obtain ⟨V, E', e, -, hgl, hU, he⟩ :=
    GlobalTheory.CompanionTheory.Unitarize.exists_unitary_image (rreg_isURepOn ε) hsub c hc h0
  exact ⟨V, inferInstance, inferInstance, E', hgl, hU, e, he⟩

end GlobalTheory.CompanionTheory.RgExhFin
end
end

