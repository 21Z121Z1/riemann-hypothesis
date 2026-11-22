import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf
import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.ExistsIsAlgebraicRatFuncFractionRingDedekind

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsIsoOfHighest
section
noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.LowestDataIso

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (lowK)
open CompanionTheory.D.DSIC (KUnit KStab)
open CompanionTheory.D.LK (LocFin IsMin Cyc mem_cyc cyc_stab hMultAlg)

variable {n : ℕ} {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

def fstL (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] : WithLp 2 (V × V') →ₗ[ℂ] V :=
  LinearMap.fst ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap

def sndL (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] : WithLp 2 (V × V') →ₗ[ℂ] V' :=
  LinearMap.snd ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap

def pair (x : V) (y : V') : WithLp 2 (V × V') := WithLp.toLp 2 (x, y)

@[simp] theorem fstL_pair (x : V) (y : V') : fstL V V' (pair x y) = x := rfl

@[simp] theorem sndL_pair (x : V) (y : V') : sndL V V' (pair x y) = y := rfl

theorem ext2 {x y : WithLp 2 (V × V')} (h₁ : fstL V V' x = fstL V V' y) (h₂ : sndL V V' x = sndL V V' y) : x = y :=
  WithLp.ofLp_injective _ (Prod.ext h₁ h₂)

theorem inner_eq (x y : WithLp 2 (V × V')) :
    ⟪x, y⟫_ℂ = ⟪fstL V V' x, fstL V V' y⟫_ℂ + ⟪sndL V V' x, sndL V V' y⟫_ℂ :=
  WithLp.prod_inner_apply x y

def sumE (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ V') (a b : Fin n) :
    Module.End ℂ (WithLp 2 (V × V')) :=
  (WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap ∘ₗ (E a b).prodMap (E' a b) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap

variable {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}

@[simp] theorem fstL_sumE (a b : Fin n) (x : WithLp 2 (V × V')) :
    fstL V V' (sumE E E' a b x) = E a b (fstL V V' x) := rfl

@[simp] theorem sndL_sumE (a b : Fin n) (x : WithLp 2 (V × V')) :
    sndL V V' (sumE E E' a b x) = E' a b (sndL V V' x) := rfl

theorem glRel_sumE (hE : GlRel E) (hE' : GlRel E') : GlRel (sumE E E') := by
  intro a b c d
  refine LinearMap.ext fun x => ?_
  have h₁ := LinearMap.congr_fun (hE a b c d) (fstL V V' x)
  have h₂ := LinearMap.congr_fun (hE' a b c d) (sndL V V' x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h₁ h₂
  refine ext2 ?_ ?_
  · by_cases p : b = c <;> by_cases q : d = a <;> simp_all
  · by_cases p : b = c <;> by_cases q : d = a <;> simp_all

theorem kUnit_sumE {ε : Fin n → Bool} (hU : KUnit ε E) (hU' : KUnit ε E') : KUnit ε (sumE E E') := by
  intro a b hab x y
  rw [inner_eq, inner_eq, fstL_sumE, sndL_sumE, fstL_sumE, sndL_sumE, hU a b hab, hU' a b hab]

theorem locFin_sumE {ε : Fin n → Bool} (hF : LocFin ε E) (hF' : LocFin ε E') : LocFin ε (sumE E E') := by
  intro x
  obtain ⟨S, hS, hk, hx⟩ := hF (fstL V V' x)
  obtain ⟨S', hS', hk', hx'⟩ := hF' (sndL V V' x)
  have hfg : (S.prod S').FG :=
    Submodule.FG.prod (Module.Finite.iff_fg.1 hS) (Module.Finite.iff_fg.1 hS')
  refine ⟨(S.prod S').map (WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap,
    Module.Finite.iff_fg.2 (hfg.map _), ?_, ?_⟩
  · rintro a b hab _ ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    exact ⟨(E a b y.1, E' a b y.2), ⟨hk a b hab _ hy₁, hk' a b hab _ hy₂⟩, rfl⟩
  · exact ⟨(fstL V V' x, sndL V V' x), ⟨hx, hx'⟩, rfl⟩

theorem kHighest_fst {ε : Fin n → Bool} {μ : Fin n → ℝ} {x : WithLp 2 (V × V')}
    (h : KHighest ε (sumE E E') μ x) : KHighest ε E μ (fstL V V' x) :=
  ⟨fun a => by rw [← fstL_sumE (E' := E'), h.1 a, map_smul],
    fun a b hab he => by rw [← fstL_sumE (E' := E'), h.2 a b hab he, map_zero]⟩

theorem kHighest_snd {ε : Fin n → Bool} {μ : Fin n → ℝ} {x : WithLp 2 (V × V')}
    (h : KHighest ε (sumE E E') μ x) : KHighest ε E' μ (sndL V V' x) :=
  ⟨fun a => by rw [← sndL_sumE (E := E), h.1 a, map_smul],
    fun a b hab he => by rw [← sndL_sumE (E := E), h.2 a b hab he, map_zero]⟩

theorem kHighest_pair {ε : Fin n → Bool} {μ : Fin n → ℝ} {x : V} {y : V'} (h : KHighest ε E μ x)
    (h' : KHighest ε E' μ y) : KHighest ε (sumE E E') μ (pair x y) :=
  ⟨fun a => ext2 (by simpa using h.1 a) (by simpa using h'.1 a),
    fun c d hcd he => ext2 (by simpa using h.2 c d hcd he) (by simpa using h'.2 c d hcd he)⟩

theorem isMin_sumE {ε : Fin n → Bool} {lam : Fin n → ℝ} (hM : IsMin ε E lam) (hM' : IsMin ε E' lam) :
    IsMin ε (sumE E E') lam := by
  intro μ x hx h
  by_cases h₁ : fstL V V' x = 0
  · refine hM' μ _ (fun h₂ => hx ?_) (kHighest_snd h)
    exact ext2 (by simpa using h₁) (by simpa using h₂)
  · exact hM μ _ h₁ (kHighest_fst h)

theorem exists_iso_of_highest {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) (hE : GlRel E)
    (hE' : GlRel E') (hU : KUnit ε E) (hU' : KUnit ε E') (hF : LocFin ε E) (hF' : LocFin ε E')
    (hM : IsMin ε E lam) (hM' : IsMin ε E' lam)
    (hS : ∀ S : Submodule ℂ V, (∀ a b, ∀ x ∈ S, E a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hS' : ∀ S : Submodule ℂ V', (∀ a b, ∀ x ∈ S, E' a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    {v₁ : V} {v₂ : V'} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) (k₁ : KHighest ε E (lowK ε lam) v₁)
    (k₂ : KHighest ε E' (lowK ε lam) v₂) :
    ∃ e : V ≃ₗ[ℂ] V', ∀ a b x, e (E a b x) = E' a b (e x) := by
  set v : WithLp 2 (V × V') := pair v₁ v₂ with hv
  have hv0 : v ≠ 0 := fun h => h₁ (show fstL V V' v = 0 by rw [h, map_zero])
  have hvk : KHighest ε (sumE E E') (lowK ε lam) v := kHighest_pair k₁ k₂
  have hone : ∀ w ∈ Cyc (sumE E E') v, KHighest ε (sumE E E') (lowK ε lam) w → ∃ c : ℂ, w = c • v :=
    fun w hw hh => hMultAlg n ε lam _ (sumE E E') hlam (glRel_sumE hE hE') (kUnit_sumE hU hU')
      (locFin_sumE hF hF') (isMin_sumE hM hM') v w hv0 hvk hh hw
  set C := Cyc (sumE E E') v with hC
  have hvC : v ∈ C := mem_cyc.2 ⟨1, by simp⟩
  have hst : ∀ a b, ∀ w ∈ C, sumE E E' a b w ∈ C := fun a b w hw => cyc_stab a b hw

  have hp₁ : C.map (fstL V V') = ⊤ := by
    refine (hS _ ?_).resolve_left fun h => h₁ ?_
    · rintro a b _ ⟨w, hw, rfl⟩
      exact ⟨_, hst a b w hw, rfl⟩
    · have : v₁ ∈ C.map (fstL V V') := ⟨v, hvC, rfl⟩
      rwa [h, Submodule.mem_bot] at this
  have hp₂ : C.map (sndL V V') = ⊤ := by
    refine (hS' _ ?_).resolve_left fun h => h₂ ?_
    · rintro a b _ ⟨w, hw, rfl⟩
      exact ⟨_, hst a b w hw, rfl⟩
    · have : v₂ ∈ C.map (sndL V V') := ⟨v, hvC, rfl⟩
      rwa [h, Submodule.mem_bot] at this

  have hno₁ : pair v₁ (0 : V') ∉ C := by
    intro h
    obtain ⟨c, hc⟩ := hone _ h (kHighest_pair k₁ ⟨fun a => by simp, fun a b _ _ => by simp⟩)
    have e₁ : v₁ = c • v₁ := by simpa [hv] using congrArg (fstL V V') hc
    have e₂ : (0 : V') = c • v₂ := by simpa [hv] using congrArg (sndL V V') hc
    rcases smul_eq_zero.1 e₂.symm with rfl | h
    · exact h₁ (by simpa using e₁)
    · exact h₂ h
  have hno₂ : pair (0 : V) v₂ ∉ C := by
    intro h
    obtain ⟨c, hc⟩ := hone _ h (kHighest_pair ⟨fun a => by simp, fun a b _ _ => by simp⟩ k₂)
    have e₁ : (0 : V) = c • v₁ := by simpa [hv] using congrArg (fstL V V') hc
    have e₂ : v₂ = c • v₂ := by simpa [hv] using congrArg (sndL V V') hc
    rcases smul_eq_zero.1 e₁.symm with rfl | h
    · exact h₂ (by simpa using e₂)
    · exact h₁ h
  have hsplit : pair v₁ (0 : V') + pair (0 : V) v₂ = v := ext2 (by simp [hv]) (by simp [hv])

  let K₁ : Submodule ℂ V :=
    C.comap ((WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap ∘ₗ LinearMap.inl ℂ V V')
  let K₂ : Submodule ℂ V' :=
    C.comap ((WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap ∘ₗ LinearMap.inr ℂ V V')
  have mem₁ : ∀ x, x ∈ K₁ ↔ pair x (0 : V') ∈ C := fun x => Iff.rfl
  have mem₂ : ∀ y, y ∈ K₂ ↔ pair (0 : V) y ∈ C := fun y => Iff.rfl
  have hK₁ : K₁ = ⊥ := by
    refine (hS K₁ fun a b x hx => ?_).resolve_right fun h => hno₂ ?_
    · rw [mem₁] at hx ⊢
      have := hst a b _ hx
      have e : sumE E E' a b (pair x (0 : V')) = pair (E a b x) (0 : V') := ext2 (by simp) (by simp)
      rwa [e] at this
    · have : pair v₁ (0 : V') ∈ C := (mem₁ _).1 (h ▸ Submodule.mem_top)
      have h' := C.sub_mem hvC this
      rwa [← hsplit, add_sub_cancel_left] at h'
  have hK₂ : K₂ = ⊥ := by
    refine (hS' K₂ fun a b x hx => ?_).resolve_right fun h => hno₁ ?_
    · rw [mem₂] at hx ⊢
      have := hst a b _ hx
      have e : sumE E E' a b (pair (0 : V) x) = pair (0 : V) (E' a b x) := ext2 (by simp) (by simp)
      rwa [e] at this
    · have : pair (0 : V) v₂ ∈ C := (mem₂ _).1 (h ▸ Submodule.mem_top)
      have h' := C.sub_mem hvC this
      rwa [← hsplit, add_sub_cancel_right] at h'

  let q₁ : C →ₗ[ℂ] V := (fstL V V').comp C.subtype
  let q₂ : C →ₗ[ℂ] V' := (sndL V V').comp C.subtype
  have b₁ : Function.Bijective q₁ := by
    refine ⟨(injective_iff_map_eq_zero q₁).2 fun w hw => ?_, fun x => ?_⟩
    · have hw' : fstL V V' (w : WithLp 2 (V × V')) = 0 := hw
      have e : (w : WithLp 2 (V × V')) = pair (0 : V) (sndL V V' w) := ext2 (by simpa using hw') (by simp)
      have : sndL V V' w ∈ K₂ := (mem₂ _).2 (e ▸ w.2)
      rw [hK₂, Submodule.mem_bot] at this
      exact Subtype.ext (by rw [e, this]; exact ext2 (by simp) (by simp))
    · obtain ⟨w, hw, rfl⟩ : x ∈ C.map (fstL V V') := hp₁ ▸ Submodule.mem_top
      exact ⟨⟨w, hw⟩, rfl⟩
  have b₂ : Function.Bijective q₂ := by
    refine ⟨(injective_iff_map_eq_zero q₂).2 fun w hw => ?_, fun x => ?_⟩
    · have hw' : sndL V V' (w : WithLp 2 (V × V')) = 0 := hw
      have e : (w : WithLp 2 (V × V')) = pair (fstL V V' w) (0 : V') := ext2 (by simp) (by simpa using hw')
      have : fstL V V' w ∈ K₁ := (mem₁ _).2 (e ▸ w.2)
      rw [hK₁, Submodule.mem_bot] at this
      exact Subtype.ext (by rw [e, this]; exact ext2 (by simp) (by simp))
    · obtain ⟨w, hw, rfl⟩ : x ∈ C.map (sndL V V') := hp₂ ▸ Submodule.mem_top
      exact ⟨⟨w, hw⟩, rfl⟩
  let f₁ : C ≃ₗ[ℂ] V := LinearEquiv.ofBijective q₁ b₁
  let f₂ : C ≃ₗ[ℂ] V' := LinearEquiv.ofBijective q₂ b₂
  refine ⟨f₁.symm.trans f₂, fun a b x => ?_⟩
  obtain ⟨w, rfl⟩ := f₁.surjective x
  have e : E a b (f₁ w) = f₁ ⟨sumE E E' a b w, hst a b w w.2⟩ := rfl
  rw [e]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem algUniq : CompanionTheory.RgExh.Fin.AlgUniq := by
  intro n ε V V' _ _ _ _ E E' hE hE' s mu hU hU' hF hF' hS hS' hD hD'
  obtain ⟨hP, -, hM, v₁, h₁, k₁⟩ := hD
  obtain ⟨-, -, hM', v₂, h₂, k₂⟩ := hD'
  have gl : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] {F : Fin n → Fin n → Module.End ℂ W}, GlRel F →
      GlRel fun a b => F (s a) (s b) := by
    intro W _ _ F hF a b c d
    simpa only [s.injective.eq_iff] using hF (s a) (s b) (s c) (s d)
  have un : ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {F : Fin n → Fin n → Module.End ℂ W},
      IsUnitary ε F → KUnit (ε ∘ s) fun a b => F (s a) (s b) := by
    intro W _ _ F hF a b hab x y
    have hab' : ε (s a) = ε (s b) := hab
    rw [hF (s a) (s b) x y]
    simp [Formalism.REAL.sgn, hab']
  have lf : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] {F : Fin n → Fin n → Module.End ℂ W}, LocFin ε F →
      LocFin (ε ∘ s) fun a b => F (s a) (s b) := by
    intro W _ _ F hF x
    obtain ⟨S, hS, hk, hx⟩ := hF x
    exact ⟨S, hS, fun a b hab y hy => hk (s a) (s b) hab y hy, hx⟩
  have si : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] {F : Fin n → Fin n → Module.End ℂ W},
      (∀ S : Submodule ℂ W, (∀ a b, ∀ x ∈ S, F a b x ∈ S) → S = ⊥ ∨ S = ⊤) →
      ∀ S : Submodule ℂ W, (∀ a b, ∀ x ∈ S, F (s a) (s b) x ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro W _ _ F hF S hst
    refine hF S fun a b x hx => ?_
    simpa using hst (s.symm a) (s.symm b) x hx
  obtain ⟨e, he⟩ := exists_iso_of_highest (ε := ε ∘ s) (lam := mu) (E := fun a b => E (s a) (s b))
    (E' := fun a b => E' (s a) (s b)) hP.1 (gl hE) (gl hE') (un hU) (un hU') (lf hF) (lf hF') hM hM'
    (si hS.2) (si hS'.2) h₁ h₂ k₁ k₂
  refine ⟨e, fun a b x => ?_⟩
  simpa using he (s.symm a) (s.symm b) x

end GlobalTheory.CompanionTheory.LowestDataIso
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPermOfCapPEq
section
open Formalism.REAL

noncomputable section

namespace GlobalTheory.CompanionTheory.CharOfLowK

theorem roots_prod_X_sub_C {n : ℕ} (k : Fin n → ℂ) :
    (∏ a, (Polynomial.X - Polynomial.C (k a))).roots = Multiset.map k Finset.univ.val := by
  have hprod : (∏ a, (Polynomial.X - Polynomial.C (k a))) =
      ((Multiset.map k Finset.univ.val).map fun x => Polynomial.X - Polynomial.C x).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]

theorem exists_perm_of_capelliPolynomial_eq {n : ℕ} (f g : Fin n → ℂ)
    (h : ∀ Y, Formalism.QuantumDeterminants.capP f Y = Formalism.QuantumDeterminants.capP g Y) :
    ∃ τ : Equiv.Perm (Fin n), ∀ a, f a = g (τ a) := by
  classical
  have hp : (∏ a, (Polynomial.X - Polynomial.C (-f a))) = ∏ a, (Polynomial.X - Polynomial.C (-g a)) := by
    apply Polynomial.funext
    intro Y
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_neg_eq_add]
    exact h Y
  have hmap : Multiset.map (fun a => -f a) Finset.univ.val = Multiset.map (fun a => -g a) Finset.univ.val := by
    rw [← roots_prod_X_sub_C (fun a => -f a), ← roots_prod_X_sub_C (fun a => -g a)]
    exact congrArg Polynomial.roots hp
  have hcard : ∀ c : ℂ, Fintype.card {a // -f a = c} = Fintype.card {a // -g a = c} := by
    intro c
    have hc := congrArg (Multiset.count c) hmap
    rw [Multiset.count_map, Multiset.count_map] at hc
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card, Finset.card, Finset.filter_val,
      Finset.filter_val]
    convert hc using 3 <;> simp [eq_comm]
  let e : ∀ c, {a // -f a = c} ≃ {a // -g a = c} := fun c => Fintype.equivOfCardEq (hcard c)
  let τ : Equiv.Perm (Fin n) :=
    ((Equiv.sigmaFiberEquiv (fun a => -f a)).symm.trans (Equiv.sigmaCongrRight e)).trans
      (Equiv.sigmaFiberEquiv (fun a => -g a))
  refine ⟨τ, fun a => ?_⟩
  have key : -g (τ a) = -f a := (e (-f a) ⟨a, rfl⟩).2
  exact neg_inj.mp key.symm

theorem charOfAlgDS : CompanionTheory.RgExh.Fin.CharOfAlgDS := by
  intro n ε V _ _ E hE χ s mu hU hLF hSC hDS
  obtain ⟨hHC, -, hMin, v, hv0, hKH⟩ := hDS
  obtain ⟨S, hSfin, hSK, hvS⟩ := hLF v
  have hU' : Formalism.REAL.IsUnitary (ε ∘ s) (fun a b => E (s a) (s b)) := fun a b x y => hU (s a) (s b) x y
  have hSK' : CompanionTheory.D.DSIC.KStab (ε ∘ s) (fun a b => E (s a) (s b)) S :=
    fun a b hab w hw => hSK (s a) (s b) hab w hw
  have hcap : ∀ Y, Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y = Formalism.QuantumDeterminants.capP χ Y := by
    intro Y
    have h1 := CompanionTheory.D.DSIC.hAlgCore n (ε ∘ s) mu V (fun a b => E (s a) (s b)) v S hHC
      (GlobalTheory.CompanionTheory.HolCoef.CapLW.glRel_perm hE s) hU' hKH hSfin hSK' hvS hMin Y
    rw [GlobalTheory.CompanionTheory.HolCoef.CapLW.qdet_perm hE s] at h1
    have h2 : Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • 1 := hSC Y
    have h3 : Formalism.QuantumDeterminants.capP χ Y • v = Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y • v := by
      rw [← h1, h2]
      simp
    exact (smul_left_injective ℂ hv0 h3).symm
  exact exists_perm_of_capelliPolynomial_eq (fun a => (mu a : ℂ)) χ hcap

end GlobalTheory.CompanionTheory.CharOfLowK
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniqueParam
section
open Finset

namespace GlobalTheory.CompanionTheory.ArrCount

theorem exists_unique_param {n : ℕ} (χ : Fin n → ℂ) (hχ : Function.Injective χ)
    (h : ∀ a, (χ a).im = 0 ∧ ∃ m : ℤ, (χ a).re - ((n : ℝ) - 1) / 2 = m) :
    ∃ μ : Fin n → ℝ, ∀ m : Fin n → ℝ,
      (Formalism.QuantumDeterminants.IsHCParam m ∧ ∃ τ : Equiv.Perm (Fin n), ∀ a, ((m a : ℝ) : ℂ) = χ (τ a)) ↔ m = μ := by
  have hval : ∀ a, (((χ a).re : ℝ) : ℂ) = χ a := fun a => Complex.ext (by simp) (by simp [(h a).1])
  let r : Fin n → ℝ := fun a => (χ a).re
  have hr : Function.Injective r := fun a b hab => hχ (by
    rw [← hval a, ← hval b]; exact congrArg _ hab)
  let τ₀ : Equiv.Perm (Fin n) := Fin.revPerm.trans (Tuple.sort r)
  have hmono : StrictMono (r ∘ Tuple.sort r) :=
    (Tuple.monotone_sort r).strictMono_of_injective (hr.comp (Tuple.sort r).injective)
  have hanti : StrictAnti (r ∘ τ₀) := fun a b hab => hmono (Fin.rev_lt_rev.2 hab)
  refine ⟨r ∘ τ₀, fun m => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨hm, -⟩, τ, hτ⟩
    have hmr : ∀ a, m a = r (τ a) := fun a => by
      have e := hτ a
      rw [← hval] at e
      exact_mod_cast e
    let σ : Equiv.Perm (Fin n) := τ.trans τ₀.symm
    have hσ : ∀ a, m a = (r ∘ τ₀) (σ a) := fun a => by simp [σ, hmr]
    have hσm : StrictMono σ := fun a b hab => by
      have e := hm hab
      rw [hσ a, hσ b] at e
      exact hanti.lt_iff_gt.1 e
    have hid : (σ : Fin n → Fin n) = id :=
      (StrictMono.range_inj hσm strictMono_id).1 (by simp [σ.surjective.range_eq])
    funext a
    rw [hσ a, hid]
    rfl
  · rintro rfl
    exact ⟨⟨hanti, fun a => (h _).2⟩, τ₀, fun a => hval _⟩

theorem arrCount : CompanionTheory.RgExh.Fin.ArrCount := by
  classical
  intro n ε χ χ' hχ hχ' h h'
  obtain ⟨μ, hμ⟩ := exists_unique_param χ hχ h
  obtain ⟨μ', hμ'⟩ := exists_unique_param χ' hχ' h'
  let P : Finset (Equiv.Perm (Fin n)) :=
    univ.filter fun s => ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b
  have key : ∀ (ψ : Fin n → ℂ) (ν : Fin n → ℝ),
      (∀ m : Fin n → ℝ, (Formalism.QuantumDeterminants.IsHCParam m ∧
        ∃ τ : Equiv.Perm (Fin n), ∀ a, ((m a : ℝ) : ℂ) = ψ (τ a)) ↔ m = ν) →
      ∀ d : Equiv.Perm (Fin n) × (Fin n → ℝ), d ∈ P.image (fun s => (s, ν)) ↔
        (Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
          ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = ψ (τ a)) := by
    rintro ψ ν hν ⟨s, m⟩
    constructor
    · intro hd
      obtain ⟨t, ht, e⟩ := mem_image.1 hd
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      obtain ⟨h1, h2⟩ := (hν _).2 rfl
      exact ⟨h1, (mem_filter.1 ht).2, h2⟩
    · rintro ⟨h1, h2, h3⟩
      have e : m = ν := (hν m).1 ⟨h1, h3⟩
      exact mem_image.2 ⟨s, mem_filter.2 ⟨mem_univ _, h2⟩, by simp [e]⟩
  have hinj : ∀ ν : Fin n → ℝ, Function.Injective
      (fun s : Equiv.Perm (Fin n) => (s, ν)) := fun ν a b e => (Prod.mk.inj e).1
  refine ⟨P.image fun s => (s, μ), P.image fun s => (s, μ'), ?_, key χ μ hμ, key χ' μ' hμ'⟩
  rw [card_image_of_injective _ (hinj μ), card_image_of_injective _ (hinj μ')]

end GlobalTheory.CompanionTheory.ArrCount
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimensionalComapSubtype
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgSteps

open CompanionTheory.RgExh
open Formalism.REAL (GlRel IsWeight)
open CompanionTheory.D.LK (LocFin)
open CompanionTheory.D.DSIC (KStab)

variable {n : ℕ}

theorem locFin_tens (ε : Fin n → Bool) (X : GMod n) (h : LocFin ε X.E) : LocFin ε (tens X).E := by
  intro u
  choose S hSfd hSst hSmem using fun i => h (u i)
  haveI : ∀ i, FiniteDimensional ℂ (S i) := hSfd
  have hTst : ∀ a b, ε a = ε b → ∀ x ∈ ⨆ i, S i, X.E a b x ∈ ⨆ i, S i := by
    intro a b hab x hx
    refine Submodule.iSup_induction S (motive := fun y => X.E a b y ∈ ⨆ i, S i) hx
      (fun i y hy => (le_iSup S i) (hSst i a b hab y hy)) (by simp) ?_
    intro y w hy hw
    rw [map_add]
    exact Submodule.add_mem _ hy hw
  have hfd : FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) := by
    let f : (Submodule.pi Set.univ fun _ : Fin n => ⨆ i, S i) →ₗ[ℂ] (Fin n → ↥(⨆ i, S i)) :=
      { toFun := fun v i => ⟨v.1 i, v.2 i (Set.mem_univ i)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective f
      (fun v w hvw => Subtype.ext (funext fun i => congrArg Subtype.val (congrFun hvw i)))
  refine ⟨Submodule.pi Set.univ (fun _ : Fin n => ⨆ i, S i), hfd, ?_, ?_⟩
  · intro a b hab v hv i _
    have hv' : ∀ j, v j ∈ ⨆ i, S i := fun j => hv j (Set.mem_univ j)
    change X.E a b (v i) + (if i = a then v b else 0) ∈ ⨆ i, S i
    refine Submodule.add_mem _ (hTst a b hab _ (hv' i)) ?_
    split_ifs
    · exact hv' b
    · exact Submodule.zero_mem _
  · intro i _
    exact (le_iSup S i) (hSmem i)

theorem finiteDimensional_comap_subtype {V : Type} [AddCommGroup V] [Module ℂ V]
    (S T : Submodule ℂ V) [FiniteDimensional ℂ T] : FiniteDimensional ℂ (T.comap S.subtype) := by
  refine FiniteDimensional.of_injective
    (LinearMap.codRestrict T (S.subtype ∘ₗ (T.comap S.subtype).subtype) fun x => x.2) ?_
  intro x y hxy
  have hv : ((x : S) : V) = ((y : S) : V) := congrArg (fun w : T => (w : V)) hxy
  exact Subtype.ext (Subtype.ext hv)

theorem locFin_sub (ε : Fin n → Bool) (X : GMod n) (S : Submodule ℂ X.V)
    (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) (hX : LocFin ε X.E) : LocFin ε (X.sub S h).E := by
  intro x
  obtain ⟨F, hF, hst, hx⟩ := hX x.1
  haveI := hF
  refine ⟨F.comap S.subtype, finiteDimensional_comap_subtype S F, ?_, hx⟩
  intro a b hab v hv
  exact hst a b hab v.1 hv

theorem intWt_tens (X : GMod n) (h : IntWt X) : IntWt (tens X) := by
  intro μ u hu hw a
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc
    exact hu (funext fun j => by_contra fun hj => hc ⟨j, hj⟩)
  have hw' : Formalism.REAL.IsWeight X.E (fun b => if b = i then μ b - 1 else μ b) (u i) := by
    intro b
    have hb : X.E b b (u i) + (if i = b then u b else 0) = (μ b : ℂ) • u i := congrFun (hw b) i
    by_cases hbi : b = i
    · subst hbi
      simp only [if_true] at hb ⊢
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, ← hb]
      exact (add_sub_cancel_right _ _).symm
    · simp only [if_neg hbi, if_neg (Ne.symm hbi), add_zero] at hb ⊢
      exact hb
  obtain ⟨m, hm⟩ := h _ (u i) hi hw' a
  by_cases hai : a = i
  · subst hai
    simp only [if_true] at hm
    exact ⟨m + 1, by push_cast; linarith⟩
  · simp only [if_neg hai] at hm
    exact ⟨m, hm⟩

theorem intWt_sub (X : GMod n) (S : Submodule ℂ X.V) (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S)
    (hX : IntWt X) : IntWt (X.sub S h) := by
  intro μ x hx hw a
  exact hX μ x.1 (fun h0 => hx (Subtype.ext h0)) (fun b => congrArg Subtype.val (hw b)) a

theorem locFin_step (ε : Fin n → Bool) (X : GMod n) (z : ℂ) (h : LocFin ε X.E) :
    LocFin ε (step X z).E := by
  exact locFin_sub ε (CompanionTheory.RgExh.tens X) _ _ (locFin_tens ε X h)

theorem intWt_step (X : GMod n) (z : ℂ) (h : IntWt X) : IntWt (step X z) := by
  exact intWt_sub (CompanionTheory.RgExh.tens X) _ _ (intWt_tens X h)

theorem pathFin : CompanionTheory.RgExh.Fin.PathFin := by
  intro n ε X χ ss
  induction ss generalizing X χ with
  | nil => exact ⟨id, id⟩
  | cons s ss ih =>
    constructor
    · intro h
      first
        | exact (ih _ _).1 (locFin_step ε X _ h)
        | exact locFin_step ε _ _ ((ih X χ).1 h)
        | exact locFin_step ε _ _ ((ih _ _).1 h)
    · intro h
      first
        | exact (ih _ _).2 (intWt_step X _ h)
        | exact intWt_step _ _ ((ih X χ).2 h)
        | exact intWt_step _ _ ((ih _ _).2 h)

end GlobalTheory.CompanionTheory.RgSteps
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KModOf
section
namespace GlobalTheory.CompanionTheory.KModOfStep

theorem kModOf : CompanionTheory.RgExh.Fin.KModOf := by
  intro n ε H _ _ _ σ hU hI
  exact CompanionTheory.D.LK.hKModExists n ε H σ hU hI

end GlobalTheory.CompanionTheory.KModOfStep
end

