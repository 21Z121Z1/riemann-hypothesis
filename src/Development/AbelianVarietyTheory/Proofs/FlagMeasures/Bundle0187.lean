import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0021
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CentralMapMemIntegralUnipotentFixingFrame
section
noncomputable section

namespace GlobalTheory.LoopC.Centre

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def nil (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) : S.V →ₗ[E] S.V :=
  ∑ a, ∑ a', (c a a' • S.hT (e a')).smulRight (e a)

theorem nil_apply (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) (x : S.V) :
    nil e c x = ∑ a, ∑ a', (c a a' * S.hT (e a') x) • e a := by
  simp [nil]

theorem nil_eq_zero (e : Fin r → S.V) (c : Matrix (Fin r) (Fin r) E) (x : S.V)
    (hx : ∀ a, S.hT (e a) x = 0) : nil e c x = 0 := by
  rw [nil_apply]
  simp [hx]

theorem hT_nil (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (x : S.V) (a : Fin r) : S.hT (e a) (nil e c x) = 0 := by
  rw [nil_apply, map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun b' _ => ?_
  rw [LinearMap.map_smul, he, smul_zero]

def cen (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E) :
    S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinear (LinearMap.id + nil e c) (LinearMap.id - nil e c)
    (by
      ext x
      simp [nil_eq_zero e c _ (hT_nil e he c x)])
    (by
      ext x
      simp [nil_eq_zero e c _ (hT_nil e he c x)])

theorem cen_apply (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (x : S.V) : cen e he c x = x + nil e c x := rfl

theorem cen_symm_apply (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0)
    (c : Matrix (Fin r) (Fin r) E) (x : S.V) : (cen e he c).symm x = x - nil e c x := rfl

theorem cen_isom (e : Fin r → S.V) (he : ∀ a b, S.hT (e a) (e b) = 0) (c : Matrix (Fin r) (Fin r) E)
    (hc : cᴴ = -c) : cen e he c ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  have hstar : ∀ a a', starRingEnd E (c a a') = -c a' a := by
    intro a a'
    have h := congrFun (congrFun hc a') a
    rw [starRingEnd_apply]
    simpa [Matrix.conjTranspose_apply] using h
  have hsym : ∀ u v, starRingEnd E (S.hT u v) = S.hT v u := S.herm.eq

  have hnn : ∀ x y, S.hT (nil e c x) (nil e c y) = 0 := by
    intro x y
    rw [nil_apply e c x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun a' _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hT_nil e he c y a, smul_zero]

  have hcross : ∀ x y, S.hT (nil e c x) y + S.hT x (nil e c y) = 0 := by
    intro x y
    simp only [nil_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      LinearMap.map_smul, smul_eq_mul, map_mul, RingHom.id_apply, hstar, hsym]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a' _ => ?_
    ring
  show ∀ x y, S.hT (cen e he c x) (cen e he c y) = S.hT x y
  intro x y
  rw [cen_apply, cen_apply]
  simp only [map_add, LinearMap.add_apply]
  rw [hnn, add_zero]
  linear_combination hcross x y

theorem nil_mem (Λ : Submodule (𝓞 E) S.V) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (e : Fin r → S.V)
    (heΛ : ∀ a, e a ∈ Λ) (c : Matrix (Fin r) (Fin r) (𝓞 E)) (x : S.V) (hx : x ∈ Λ) :
    nil e (c.map (algebraMap (𝓞 E) E)) x ∈ Λ := by
  rw [nil_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun a' _ => ?_
  have hd : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    have h' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hΛ
    rw [h']
    exact hx
  have h1 : S.hT (e a') x ∈ (1 : Submodule (𝓞 E) E) := by
    have h2 := (Submodule.mem_iInf _).mp hd (e a')
    have h3 := (Submodule.mem_iInf _).mp h2 (heΛ a')
    exact h3
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
  rw [Matrix.map_apply, ← ho, ← map_mul, algebraMap_smul]
  exact Λ.smul_mem _ (heΛ a)

theorem centre_gen {T : E} (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (heΛ : ∀ a, F.fl.e a ∈ Λ)
    (c : Matrix (Fin r) (Fin r) (𝓞 E))
    (hc : (c.map (algebraMap (𝓞 E) E))ᴴ = -c.map (algebraMap (𝓞 E) E)) :
    ∃ n : S.V ≃ₗ[E] S.V, (n ∈ NLam Λ F ∧ ∀ b, n (frame F b) = frame F b) ∧
      (∀ x ∈ orth S (Xsp F), n x = x) ∧
      ∀ x, n x = x + ∑ a, ∑ a', ((c a a' : E) * S.hT (F.fl.e a') x) • F.fl.e a := by
  have hiso : ∀ a b, S.hT (F.fl.e a) (F.fl.e b) = 0 := F.fl.e_iso

  have hXz : ∀ a', ∀ x ∈ Xsp F, S.hT (F.fl.e a') x = 0 := by
    intro a' x hx
    have hle : Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a')) := by
      show Submodule.span E (Set.range F.fl.e) ≤ _
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact LinearMap.mem_ker.mpr (hiso a' b)
    exact LinearMap.mem_ker.mp (hle hx)
  have hXe : ∀ a, F.fl.e a ∈ Xsp F := by
    intro a
    show F.fl.e a ∈ Submodule.span E (Set.range F.fl.e)
    exact Submodule.subset_span ⟨a, rfl⟩

  have hfix : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x = x := by
    intro x hx
    rw [cen_apply, nil_eq_zero _ _ _ ?_, add_zero]
    intro a'
    have h2 := (Submodule.mem_iInf _).mp hx (F.fl.e a')
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h2 (hXe a'))

  have hframe : ∀ b, cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) (frame F b) = frame F b := by
    intro b
    rw [cen_apply, nil_eq_zero _ _ _ ?_, add_zero]
    intro a'
    induction b using Fin.lastCases with
    | last => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using F.fl.z_orth a'
    | cast i => simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using hiso a' i

  have hflag : ∀ j, ∀ x ∈ Xflag F (j + 1),
      cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xflag F j := by
    intro j x hx
    have hle : Xflag F (j + 1) ≤ Xsp F := by
      show Submodule.span E (F.fl.e '' {i | i.1 < j + 1}) ≤ Submodule.span E (Set.range F.fl.e)
      exact Submodule.span_mono (Set.image_subset_range _ _)
    rw [cen_apply, nil_eq_zero _ _ _ (fun a' => hXz a' x (hle hx)), add_zero, sub_self]
    exact zero_mem _
  have horth : ∀ x ∈ orth S (Xsp F), cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x - x ∈ Xsp F := by
    intro x hx
    rw [hfix x hx, sub_self]
    exact zero_mem _

  have hmap : Formalism.HermitianLatticesTheory.gmap (cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E))) Λ = Λ := by
    show Submodule.map _ Λ = Λ
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) x ∈ Λ
      rw [cen_apply]
      exact Λ.add_mem hx (nil_mem Λ hΛ _ heΛ c x hx)
    · intro y hy
      refine Submodule.mem_map.mpr ⟨y - nil F.fl.e (c.map (algebraMap (𝓞 E) E)) y,
        Λ.sub_mem hy (nil_mem Λ hΛ _ heΛ c y hy), ?_⟩
      show cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) _ = y
      rw [← cen_symm_apply F.fl.e hiso _ y]
      exact LinearEquiv.apply_symm_apply _ y
  have hN : cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)) ∈ NLam Λ F := by
    simp only [NLam, IsAutLam, Set.mem_setOf_eq]
    exact ⟨⟨cen_isom _ _ _ hc, hmap⟩, hflag, horth⟩
  refine ⟨cen F.fl.e hiso (c.map (algebraMap (𝓞 E) E)), ⟨hN, hframe⟩, hfix, fun x => ?_⟩
  rw [cen_apply, nil_apply]
  rfl

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem centralMap_mem_integralUnipotentFixingFrame : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (Λ : LatV D), Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ → (∀ a, F.fl.e a ∈ Λ) → ∀ c : Matrix (Fin D.R.rS) (Fin D.R.rS) (𝓞 D.host.E), (c.map (algebraMap (𝓞 D.host.E) D.host.E))ᴴ = -c.map (algebraMap (𝓞 D.host.E) D.host.E) → ∃ n ∈ N1 D Λ F, (∀ x ∈ orth (hS D) (Xsp F), n x = x) ∧ ∀ x, n x = x + ∑ a, ∑ a', ((c a a' : D.host.E) * (hS D).hT (F.fl.e a') x) • F.fl.e a := by
  intro D T F Λ hΛ heΛ c hc
  obtain ⟨n, h1, hfix, hform⟩ := centre_gen F Λ hΛ heΛ c hc
  exact ⟨n, h1, hfix, hform⟩

end GlobalTheory.LoopC.Centre

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerFromCoordinatesProductLaw
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovMul

open GlobalTheory.Amp.Swap GlobalTheory.DegVol.Swap

variable {k r j : ℕ}

theorem upperIn_0 (β : Fin r → ℕ) : upperIn β 0 = 1 := by
  ext a b
  by_cases h : a < b
  · simp [upperIn, upper, h, h.ne]
  · simp [upperIn, upper, h, Matrix.one_apply]

private lemma wI_eq_mI (m : Fin (k + 1)) : wI k r m = UEmb.mI k r m := Fin.ext (by simp [wI, UEmb.mI])

theorem pOf_mul_we (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a : Fin (k + 1)) (b : Fin r) :
    (pOf k r q * uEmb k r u) (wI k r a) (eI k r b) = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  refine Rad.cases3 (P := fun l => pOf k r q (wI k r a) l * uEmb k r u l (eI k r b) = 0) ?_ ?_ ?_ l
  · intro c
    simp only [pOf, Rad.pEl_we, zero_mul]
  · intro c
    rw [wI_eq_mI c, UEmb.u_me, mul_zero]
  · intro c
    rw [UEmb.u_se, mul_zero]

theorem pOf_mul_se (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (pOf k r q * uEmb k r u) (esI k r a) (eI k r b) = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  refine Rad.cases3 (P := fun l => pOf k r q (esI k r a) l * uEmb k r u l (eI k r b) = 0) ?_ ?_ ?_ l
  · intro c
    simp only [pOf, Rad.pEl_se, zero_mul]
  · intro c
    rw [wI_eq_mI c, UEmb.u_me, mul_zero]
  · intro c
    rw [UEmb.u_se, mul_zero]

private lemma crd_eI_eI (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    crd k r j β x (eI k r a) (eI k r b) = upperIn β x.1 a b := by
  simp only [crd, pTop]
  exact pOf_mul_ee _ _ a b

private lemma crd_mI_eI_eq_zero (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (m : Fin (k + 1)) (b : Fin r) :
    crd k r j β x (UEmb.mI k r m) (eI k r b) = 0 := by
  rw [← wI_eq_mI]
  simp only [crd, pTop]
  exact pOf_mul_we _ _ m b

private lemma crd_esI_eI_eq_zero (β : Fin r → ℕ) (x : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    crd k r j β x (esI k r a) (eI k r b) = 0 := by
  simp only [crd, pTop]
  exact pOf_mul_se _ _ a b

theorem upperIn_mul (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) :
    upperIn β w.1 = upperIn β p.1 * upperIn β q.1 := by
  ext a b
  have e : (crd k r j β p * crd k r j β q) (eI k r a) (eI k r b) = crd k r j β w (eI k r a) (eI k r b) := by
    rw [h]
  rw [crd_eI_eI, Matrix.mul_apply, UEmb.sum_idx] at e
  simp only [crd_mI_eI_eq_zero, crd_esI_eI_eq_zero, crd_eI_eI, mul_zero, Finset.sum_const_zero, add_zero] at e
  rw [← e, Matrix.mul_apply]

theorem upper_mul_entry (x y : UT r → ℂ) (i : UT r)
    (hx : ∀ l : UT r, l.1.2.val - l.1.1.val < i.1.2.val - i.1.1.val → x l = 0) :
    (upper x * upper y) i.1.1 i.1.2 = x i + y i := by
  obtain ⟨⟨a, b⟩, hab⟩ := i
  rw [Matrix.mul_apply, Fintype.sum_eq_add a b hab.ne]
  · simp only [upper, lt_irrefl, dif_neg, not_false_eq_true, if_true, dif_pos hab, one_mul, mul_one]
    exact add_comm _ _
  · rintro c ⟨hca, hcb⟩
    simp only [upper]
    by_cases h1 : a < c
    · by_cases h2 : c < b
      · have hl : c.val - a.val < b.val - a.val := by
          have := Fin.lt_def.mp h1; have := Fin.lt_def.mp h2; omega
        rw [dif_pos h1, hx ⟨(a, c), h1⟩ hl, zero_mul]
      · rw [dif_neg h2, if_neg hcb, mul_zero]
    · rw [dif_neg h1, if_neg (Ne.symm hca), zero_mul]

theorem first (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) (i : UTin β)
    (hi : ∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) :
    w.1 i = p.1 i + q.1 i := by
  have e := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M i.1.1.1 i.1.1.2) (upperIn_mul β p q w h)
  simp only [upperIn] at e
  rw [upper_mul_entry _ _ i.1] at e
  · simpa [upper, i.1.2, i.2] using e
  · intro l hl
    split_ifs with hβ
    · exact hi ⟨l, hβ⟩ hl
    · rfl

theorem cancel (β : Fin r → ℕ) (p q w : (UTin β → ℂ) × PTop k r j)
    (h : crd k r j β p * crd k r j β q = crd k r j β w) (hp : p.1 = 0) :
    pTop k r j p.2 * pTop k r j q.2 = pTop k r j w.2 := by
  have hm := upperIn_mul β p q w h
  rw [hp, upperIn_0, one_mul] at hm
  set U := upperIn β q.1 with hUdef
  have hT : U.IsUpperTriangular := by
    intro a b hba
    have h1 : ¬ a < b := not_lt.mpr hba.le
    have h2 : a ≠ b := ne_of_gt hba
    simp [hUdef, upperIn, upper, h1, h2]
  have hU : IsUnit U.det := by
    rw [Matrix.det_of_isUpperTriangular hT]
    simp [hUdef, upperIn, upper]
  have hV : uEmb k r U * uEmb k r U⁻¹ = 1 := by
    rw [← UEmb.uEmb_mul, Matrix.mul_nonsing_inv _ hU, UEmb.uEmb_one]
  have h' : pTop k r j p.2 * pTop k r j q.2 * uEmb k r U = pTop k r j w.2 * uEmb k r U := by
    have h2 := h
    simp only [crd, hp, upperIn_0, UEmb.uEmb_one, mul_one, hm] at h2
    rw [mul_assoc]
    exact h2
  calc pTop k r j p.2 * pTop k r j q.2
      = pTop k r j p.2 * pTop k r j q.2 * uEmb k r U * uEmb k r U⁻¹ := by rw [mul_assoc _ (uEmb k r U), hV, mul_one]
    _ = pTop k r j w.2 * uEmb k r U * uEmb k r U⁻¹ := by rw [h']
    _ = pTop k r j w.2 := by rw [mul_assoc, hV, mul_one]

private lemma eq_and_eq_of_pEl_eq (B B' : Fin r → Fin (k + 1) → ℂ) (S S' : Matrix (Fin r) (Fin r) ℂ)
    (h : pEl k r B S = pEl k r B' S') : B = B' ∧ S = S' := by
  have hB : B = B' := by
    funext b c
    simpa [Rad.pEl_ws] using
      congrArg (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => M (wI k r c) (esI k r b)) h
  subst hB
  refine ⟨rfl, ?_⟩
  ext a b
  simpa [Rad.pEl_es] using
    congrArg (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => M (eI k r a) (esI k r b)) h

theorem crd_mul : ∀ (k r j : ℕ) (β : Fin r → ℕ), crd k r j β 0 = 1 ∧ ∀ p q w : (UTin β → ℂ) × PTop k r j, crd k r j β p * crd k r j β q = crd k r j β w → (∀ i : UTin β, (∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2) := by
  intro k r j β
  refine ⟨?_, fun p q w h => ⟨fun i hi => first β p q w h i hi, fun hp => ?_, fun hp hB => ?_⟩⟩
  · have hS : skewM (r := r) (fun _ => 0) (fun _ => 0) = 0 := by
      ext a b
      simp only [skewM, Matrix.zero_apply]
      split_ifs <;> simp
    simp only [crd, Prod.fst_zero, Prod.snd_zero, upperIn_0, UEmb.uEmb_one, mul_one, pTop, pOf,
      Pi.zero_apply, dite_eq_ite, ite_self, hS]
    exact Rad.pEl_zero
  · have hc := cancel β p q w h hp
    simp only [pTop, pOf] at hc
    rw [Rad.pEl_mul] at hc
    have hB' := (eq_and_eq_of_pEl_eq _ _ _ _ hc).1
    funext a c
    have e := congrFun (congrFun hB' a.1) c
    simpa [a.2] using e.symm
  · have hc := cancel β p q w h hp
    simp only [pTop, pOf, hB, Pi.zero_apply, dite_eq_ite, ite_self] at hc
    rw [Rad.pEl_mul] at hc
    have hS' := (eq_and_eq_of_pEl_eq _ _ _ _ hc).2
    simp only [Rad.herm_Hb] at hS'
    ext x
    · obtain ⟨⟨⟨a, b⟩, hab⟩, hj⟩ := x
      have e := congrFun (congrFun hS' a) b
      simp [skewM, hab, hj] at e
      simpa using e.symm
    · obtain ⟨a, ha⟩ := x
      have e := congrArg Complex.im (congrFun (congrFun hS' a) a)
      simp [skewM, ha] at e
      simpa using e.symm

end GlobalTheory.DegVol.RefCovMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexFlagAtEmbeddingFrameFinrankAndLowers
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

private lemma linearIndependent_map_ringHom_complex {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) {ι : Type}
    [Fintype ι] {v : ι → Fin n → E} (hv : LinearIndependent E v) :
    LinearIndependent ℂ (fun i l => φ (v i l)) := by
  classical

  let f : (ι → E) →ₗ[E] (Fin n → E) := Fintype.linearCombination E v
  have hf : ∀ c, f c = ∑ i, c i • v i := fun c => Fintype.linearCombination_apply E v c
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [hf] at hc
    funext i
    exact (Fintype.linearIndependent_iff.mp hv) c hc i
  obtain ⟨L, hL⟩ := f.exists_leftInverse_of_injective hker
  have hB : ∀ i, LinearMap.toMatrix' L *ᵥ v i = Pi.single i 1 := by
    intro i
    rw [LinearMap.toMatrix'_mulVec]
    have h1 := LinearMap.congr_fun hL (Pi.single i 1)
    have h2 : f (Pi.single i 1) = v i := by
      rw [hf]
      simp [Pi.single_apply]
    rw [LinearMap.comp_apply, h2] at h1
    exact h1
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hcol : ∀ i k, ((LinearMap.toMatrix' L).map φ *ᵥ fun l => φ (v i l)) k
      = if k = i then 1 else 0 := by
    intro i k
    have h3 := RingHom.map_mulVec φ (LinearMap.toMatrix' L) (v i) k
    rw [hB i] at h3
    rw [show (fun l => φ (v i l)) = φ ∘ v i from rfl, ← h3]
    by_cases hki : k = i
    · subst hki; simp
    · simp [hki]
  have h4 := congrArg (fun w => ((LinearMap.toMatrix' L).map φ *ᵥ w) j) hc
  simp only [Matrix.mulVec_zero, Pi.zero_apply] at h4
  rw [← h4, ← Matrix.mulVecLin_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, Matrix.mulVecLin_apply, hcol, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private lemma map_mem_span_image_of_mem_span {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ)
    (t : Set (Fin n → E)) {x : Fin n → E} (hx : x ∈ Submodule.span E t) :
    (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' t) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have h0 : (fun l => φ ((0 : Fin n → E) l)) = 0 := by funext l; simp
    rw [h0]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have h1 : (fun l => φ ((y + z) l)) = (fun l => φ (y l)) + (fun l => φ (z l)) := by
      funext l; simp
    rw [h1]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have h1 : (fun l => φ ((c • y) l)) = φ c • (fun l => φ (y l)) := by
      funext l; simp
    rw [h1]
    exact Submodule.smul_mem _ _ hy

theorem finrank_span_image_ringHom {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ)
    (s : Set (Fin n → E)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' s))
      = Module.finrank E (Submodule.span E s) := by
  classical
  let V := Submodule.span E s
  let b := Module.finBasis E V
  let v : Fin (Module.finrank E V) → Fin n → E := fun i => (b i : Fin n → E)
  have hv : LinearIndependent E v := b.linearIndependent.map' V.subtype V.ker_subtype
  have hvV : ∀ i, v i ∈ V := fun i => (b i).2
  have hspan : Submodule.span E (Set.range v) = V := by
    have hr : Set.range v = V.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have heq : Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' s)
      = Submodule.span ℂ (Set.range fun i l => φ (v i l)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span E (Set.range v) := by
        rw [hspan]; exact Submodule.subset_span hx
      have h := map_mem_span_image_of_mem_span φ _ hx'
      rw [← Set.range_comp] at h
      exact h
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact map_mem_span_image_of_mem_span φ s (hvV i)
  rw [heq, finrank_span_eq_card (linearIndependent_map_ringHom_complex φ hv), Fintype.card_fin]

theorem finrank_locFlag_and_lowers (E : Type) [Field E] [NumberField E] (n : ℕ) (φ : E →+* ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (hP : IsUnit P) :
    (∀ b, Module.finrank ℂ (locFlag φ P F b) = Formalism.HN.rkK (F b)) ∧
      ∀ c, ∀ T ∈ lowers F c, P⁻¹ * T.map φ * P ∈ lowers (locFlag φ P F) c := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  refine ⟨fun b => ?_, fun c T hT => ?_⟩
  · have hinj : Function.Injective (Matrix.mulVecLin P⁻¹) := by
      intro x y hxy
      have h := congrArg (fun z => P *ᵥ z) hxy
      simpa [Matrix.mulVec_mulVec, hPP] using h
    have himg : locFlag φ P F b = Submodule.map (Matrix.mulVecLin P⁻¹)
        (Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' (F b : Set (Fin n → E)))) := by
      rw [Submodule.map_span, ← Set.image_comp]
      rfl
    rw [himg, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, finrank_span_image_ringHom]
    rfl
  · rw [GlobalTheory.RadCov.mem_lowers] at hT ⊢
    intro b y hy
    have key : locFlag φ P F (b + c + 1)
        ≤ Submodule.comap (Matrix.mulVecLin (P⁻¹ * T.map φ * P)) (locFlag φ P F b) := by
      rw [locFlag, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      refine Submodule.subset_span ⟨T *ᵥ x, hT b x hx, ?_⟩
      have h1 : (fun l => φ ((T *ᵥ x) l)) = T.map φ *ᵥ (fun l => φ (x l)) := by
        funext l; exact RingHom.map_mulVec φ T x l
      dsimp only
      rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P⁻¹ * T.map φ) P P⁻¹,
        hPP, Matrix.mul_one]
    exact key hy

end GlobalTheory.RadCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMassOneCutoffDoubleCosetIntegralStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_massOne_cutoff_doubleCoset_integral : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (K : Subgroup G) (K' : Subgroup H) (x : G) (S : Set G), IsOpen (K : Set G) → IsOpen (K' : Set H) → IsCompact (K' : Set H) → (∀ h, h ∈ K' ↔ x⁻¹ * j h * x ∈ K) → (∀ g, g ∈ S ↔ ∃ h, ∃ k ∈ K, g = j h * x * k) → ∃ b : G → ENNReal, Measurable b ∧ (∀ g, ∫⁻ h, b (j h * g) ∂ν = 1) ∧ ∫⁻ g, S.indicator 1 g * b g ∂μ = μ K / ν K' := by
  first | exact @GlobalTheory.StabUnfold.exists_cutoff_doubleCoset | exact GlobalTheory.StabUnfold.exists_cutoff_doubleCoset | (intros; apply GlobalTheory.StabUnfold.exists_cutoff_doubleCoset <;> assumption)
end

