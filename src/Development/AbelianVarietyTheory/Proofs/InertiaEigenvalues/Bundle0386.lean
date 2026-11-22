import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStabOfReps
section
noncomputable section

open Formalism.IndefR.Bridge

namespace GlobalTheory.ClassTrace

variable {O Γ Hf P : Type} [CommRing O] [Group Γ] [Group Hf] [AddCommGroup P] [Module O P]
  (ι : Γ →* Hf) (J : Subgroup Hf) (lam : J →* Oˣ) (ρ : Representation O Γ P)

def intForms (LL : Hf → Submodule O P) : Submodule O (Hf → P) where
  carrier := {f | (∀ (γ : Γ) (h : Hf) (k : J), f (ι γ * h * k) = (lam k : O) • ρ γ (f h)) ∧ ∀ h, f h ∈ LL h}
  add_mem' := fun {f g} hf hg =>
    ⟨fun γ h k => by simp only [Pi.add_apply, hf.1 γ h k, hg.1 γ h k, map_add, smul_add],
      fun h => Submodule.add_mem _ (hf.2 h) (hg.2 h)⟩
  zero_mem' := ⟨fun γ h k => by simp, fun h => Submodule.zero_mem _⟩
  smul_mem' := fun a f hf =>
    ⟨fun γ h k => by simp only [Pi.smul_apply, hf.1 γ h k, map_smul]; rw [smul_comm],
      fun h => Submodule.smul_mem _ _ (hf.2 h)⟩

def LatticeLaw (LL : Hf → Submodule O P) : Prop :=
  (∀ γ h, (LL h).map (ρ γ) = LL (ι γ * h)) ∧ ∀ h (k : J), LL (h * k) = LL h

def tr (h : Hf) (p : P) : P := ∑ᶠ γ : stab ι J h, (lam (stabK ι γ) : O) • ρ (γ : Γ) p

open Classical in

def lamExt (x : Hf) : O := if hx : x ∈ J then (lam ⟨x, hx⟩ : O) else 0

theorem lamExt_coe (k : J) : lamExt J lam (k : Hf) = (lam k : O) := by
  simp [lamExt]

theorem lamExt_of_not_mem {x : Hf} (hx : x ∉ J) : lamExt J lam x = 0 := by
  simp [lamExt, hx]

theorem lamExt_mul (x : Hf) (k : J) : lamExt J lam (x * k) = lamExt J lam x * (lam k : O) := by
  by_cases hx : x ∈ J
  · have hxk : x * (k : Hf) ∈ J := J.mul_mem hx k.2
    unfold lamExt
    rw [dif_pos hxk, dif_pos hx, ← Units.val_mul, ← map_mul]
    rfl
  · have hxk : x * (k : Hf) ∉ J := fun hm => hx (by simpa using J.mul_mem hm (J.inv_mem k.2))
    rw [lamExt_of_not_mem J lam hx, lamExt_of_not_mem J lam hxk, zero_mul]

def traceForm (h : Hf) (p : P) (x : Hf) : P := ∑ᶠ γ : Γ, lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p

def link (h x : Hf) : Set Γ := {γ | h⁻¹ * (ι γ)⁻¹ * x ∈ J}

theorem mem_link_iff {h x : Hf} {γ : Γ} : γ ∈ link ι J h x ↔ ∃ k : J, x = ι γ * h * k := by
  constructor
  · intro hγ
    refine ⟨⟨h⁻¹ * (ι γ)⁻¹ * x, hγ⟩, ?_⟩
    show x = ι γ * h * (h⁻¹ * (ι γ)⁻¹ * x)
    group
  · rintro ⟨k, rfl⟩
    show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) ∈ J
    rw [show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) = (k : Hf) by group]
    exact k.2

def linkEquiv {h x : Hf} {γ₀ : Γ} (h0 : γ₀ ∈ link ι J h x) : stab ι J x ≃ link ι J h x where
  toFun δ := ⟨δ * γ₀, by
    have h1 := J.mul_mem h0 (J.inv_mem ((mem_stab ι).1 δ.2))
    simpa [link, mul_assoc] using h1⟩
  invFun γ := ⟨γ * γ₀⁻¹, by
    have h1 := J.mul_mem (J.inv_mem γ.2) h0
    rw [mem_stab]
    simpa [link, mul_assoc] using h1⟩
  left_inv δ := by simp
  right_inv γ := by simp

theorem link_finite (hfin : ∀ x, Finite (stab ι J x)) (h x : Hf) : (link ι J h x).Finite := by
  rcases (link ι J h x).eq_empty_or_nonempty with he | ⟨γ₀, h0⟩
  · rw [he]
    exact Set.finite_empty
  · have := hfin x
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (linkEquiv ι J h0))

theorem support_subset (h : Hf) (p : P) (x : Hf) :
    (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p) ⊆ link ι J h x := by
  intro γ hγ
  rw [Function.mem_support] at hγ
  by_contra hn
  have hn' : h⁻¹ * (ι γ)⁻¹ * x ∉ J := hn
  exact hγ (by rw [lamExt_of_not_mem J lam hn', zero_smul])

theorem traceForm_eq_zero (h : Hf) (p : P) {x : Hf} (hx : ¬ ∃ (γ : Γ) (k : J), x = ι γ * h * k) :
    traceForm ι J lam ρ h p x = 0 := by
  unfold traceForm
  have hz : ∀ γ : Γ, lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p = 0 := by
    intro γ
    have hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J := fun hm =>
      hx ⟨γ, (mem_link_iff ι J (h := h) (x := x) (γ := γ)).1 hm⟩
    rw [lamExt_of_not_mem J lam hn, zero_smul]
  simp only [hz, finsum_zero]

theorem traceForm_law (hfin : ∀ x, Finite (stab ι J x)) (h : Hf) (p : P) (γ₀ : Γ) (x : Hf) (k : J) :
    traceForm ι J lam ρ h p (ι γ₀ * x * k) = (lam k : O) • ρ γ₀ (traceForm ι J lam ρ h p x) := by
  have hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite :=
    (link_finite ι J hfin h x).subset (support_subset ι J lam ρ h p x)
  unfold traceForm
  conv_rhs => rw [← LinearMap.smul_apply]
  rw [map_finsum _ hf, ← finsum_comp_equiv (Equiv.mulLeft γ₀)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulLeft]
  have e : h⁻¹ * (ι (γ₀ * γ))⁻¹ * (ι γ₀ * x * k) = h⁻¹ * (ι γ)⁻¹ * x * k := by
    rw [map_mul]
    group
  rw [e, lamExt_mul, map_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul, mul_smul]
  exact smul_comm _ _ _

variable {C W : Type} [Field C] [AddCommGroup W] [Module C W] {e : O →+* C}

def classSum (θ : Hf → P →ₛₗ[e] W) {I : Type} [Fintype I] (y : I → Hf) (f : Hf → P) : W :=
  ∑ i, (Nat.card (stab ι J (y i)) : C)⁻¹ • θ (y i) (f (y i))

def DualLaw (θ : Hf → P →ₛₗ[e] W) : Prop :=
  ∀ (γ : Γ) (h : Hf) (k : J) (p : P), e (lam k) • θ (ι γ * h * k) (ρ γ p) = θ h p

theorem kernel_traceForm (hfin : ∀ x, Finite (stab ι J x)) {θ : Hf → P →ₛₗ[e] W} (hθ : DualLaw ι J lam ρ θ)
    (h : Hf) (p : P) {x : Hf} {γ₀ : Γ} (h0 : γ₀ ∈ link ι J h x) :
    θ x (traceForm ι J lam ρ h p x) = (Nat.card (stab ι J x) : C) • θ h p := by
  classical
  have hL := link_finite ι J hfin h x
  have hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite :=
    hL.subset (support_subset ι J lam ρ h p x)
  have hterm : ∀ γ : Γ, θ x (lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p) =
      if γ ∈ link ι J h x then θ h p else 0 := by
    intro γ
    split_ifs with hγ
    · obtain ⟨k, hk⟩ := (mem_link_iff ι J).1 hγ
      have hk' : h⁻¹ * (ι γ)⁻¹ * x = (k : Hf) := by
        rw [hk]
        group
      rw [hk', lamExt_coe, map_smulₛₗ, ← hθ γ h k p, ← hk]
    · have hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J := hγ
      rw [lamExt_of_not_mem J lam hn, zero_smul, map_zero]
  have hsub : Function.support (fun γ : Γ => if γ ∈ link ι J h x then θ h p else 0) ⊆
      (hL.toFinset : Set Γ) := by
    intro γ hγ
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    exact hγ (if_neg hn)
  have hc : hL.toFinset.card = Nat.card (stab ι J x) := by
    rw [Nat.card_congr (linkEquiv ι J h0), Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hL]
  unfold traceForm
  rw [map_finsum (θ x) hf]
  simp only [hterm]
  rw [finsum_eq_sum_of_support_subset _ hsub,
    Finset.sum_congr rfl (fun γ hγ => if_pos ((Set.Finite.mem_toFinset hL).1 hγ)),
    Finset.sum_const, hc, Nat.cast_smul_eq_nsmul]

theorem classSum_traceForm [CharZero C] (hfin : ∀ x, Finite (stab ι J x)) {θ : Hf → P →ₛₗ[e] W}
    (hθ : DualLaw ι J lam ρ θ) {I : Type} [Fintype I] {y : I → Hf} (hy : IsReps ι J y) (h : Hf) (p : P) :
    classSum ι J θ y (traceForm ι J lam ρ h p) = θ h p := by
  obtain ⟨i₀, ⟨γ, k, hh⟩, huniq⟩ := hy h
  unfold classSum
  rw [Finset.sum_eq_single i₀]
  · have h0 : γ⁻¹ ∈ link ι J h (y i₀) := by
      rw [mem_link_iff]
      refine ⟨k⁻¹, ?_⟩
      rw [hh]
      simp only [map_inv, Subgroup.coe_inv]
      group
    rw [kernel_traceForm ι J lam ρ hfin hθ h p h0]
    have := hfin (y i₀)
    have hne : (Nat.card (stab ι J (y i₀)) : C) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact inv_smul_smul₀ hne _
  · intro i _ hi
    have hx : ¬ ∃ (γ' : Γ) (k' : J), y i = ι γ' * h * k' := by
      rintro ⟨γ', k', hy'⟩
      apply hi
      apply huniq
      refine ⟨γ'⁻¹, k'⁻¹, ?_⟩
      rw [hy']
      simp only [map_inv, Subgroup.coe_inv]
      group
    rw [traceForm_eq_zero ι J lam ρ h p hx, map_zero, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i₀) hi

theorem finite_stab_of_reps {I : Type} {y : I → Hf} (hy : IsReps ι J y) (hfin : ∀ i, Finite (stab ι J (y i)))
    (x : Hf) : Finite (stab ι J x) := by
  obtain ⟨i, ⟨γ, k, hx⟩, -⟩ := hy x
  subst hx
  have := hfin i
  refine Finite.of_injective (β := stab ι J (y i)) (fun δ => ⟨γ⁻¹ * δ * γ, ?_⟩) ?_
  · rw [mem_stab]
    have hδ := (mem_stab ι).1 δ.2
    have e : (y i)⁻¹ * ι (γ⁻¹ * δ * γ) * y i =
        (k : Hf) * ((ι γ * y i * k)⁻¹ * ι δ * (ι γ * y i * k)) * (k : Hf)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [e]
    exact J.mul_mem (J.mul_mem k.2 hδ) (J.inv_mem k.2)
  · intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa using this

end GlobalTheory.ClassTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqs
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.FrameEq

theorem map_inj {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (hf : Function.Injective f)
    {M M' : Matrix m n R} (h : M.map f = M'.map f) : M = M' := by
  ext i j
  exact hf (congrFun (congrFun h i) j)

private theorem padicInt_hom_ext_pt {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R]
    [IsHausdorff (Ideal.span {(l : R)}) R] (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {(l : R)}) _ fun n => ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (PadicInt.appr z n : ℤ_[l]) + c * (l : ℤ_[l]) ^ n := by rw [hc]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f c - g c, ?_⟩
  rw [hz]
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

theorem map_smul_rh {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobW_galW {l : ℕ} [Fact l.Prime] (g : GQ l) (x : WCb l) :
    frobW l (galW l g x) = galW l g (frobW l x) := by
  ext n
  simp [frobW, galW, mapAlgEquivW, mapEquivW, WittVector.map_coeff, frobenius_def, map_pow]

theorem cocycle_frob {R : Type} [CommRing R] {d N : ℕ} (fr ga : R →+* R) (hc : ∀ x, fr (ga x) = ga (fr x))
    (e : R) (T A ε Z : Matrix (Fin d) (Fin d) R) (hT : IsUnit T) (hφ : e ^ N • T.map fr = T * A)
    (hgal : Z * T.map ga = T * ε) (hZ : Z.map fr = Z) :
    e ^ N • (ε * A.map ga) = ga e ^ N • (A * ε.map fr) := by
  have h1 : ga e ^ N • T.map (fun x => ga (fr x)) = T.map ga * A.map ga := by
    have := congrArg (fun M => M.map ga) hφ
    simp only [map_smul_rh, Matrix.map_mul, Matrix.map_map, map_pow] at this
    exact this
  have h2 : Z * T.map (fun x => ga (fr x)) = T.map fr * ε.map fr := by
    have := congrArg (fun M => M.map fr) hgal
    simp only [Matrix.map_mul, Matrix.map_map, hZ] at this
    have e2 : T.map (fun x => ga (fr x)) = T.map (⇑fr ∘ ⇑ga) := by
      ext i j; simp [hc]
    rw [e2]; exact this
  apply hT.mul_left_cancel
  calc T * (e ^ N • (ε * A.map ga)) = e ^ N • (T * ε * A.map ga) := by
        rw [Matrix.mul_smul, Matrix.mul_assoc]
    _ = e ^ N • (Z * (ga e ^ N • T.map (fun x => ga (fr x)))) := by
        rw [h1, ← hgal, Matrix.mul_assoc]
    _ = ga e ^ N • ((e ^ N • T.map fr) * ε.map fr) := by
        rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, h2, Matrix.smul_mul]
    _ = T * (ga e ^ N • (A * ε.map fr)) := by
        rw [hφ, Matrix.mul_smul, Matrix.mul_assoc]

open GlobalTheory.FrameEq in

theorem frame_Y_eqs : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * F.A.map bk.ev ∧ (∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)) ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ N • (F.ε g * F.A.map (fun s => Per.σA (g : GQ l) (bk.ev s))) = Per.σA (g : GQ l) (bk.ev bk.E) ^ N • (F.A.map bk.ev * (F.ε g).map WittVector.frobenius) := by
  intro l _ K bk τ hτ N d ρ F Y Y' hY _
  have hev : ∀ s, inclW l (bk.ev s) = bk.evW s := fun s => rfl
  have hz : ∀ z : ℤ_[l], inclW l (Per.zA l z) = algebraMap ℤ_[l] (WCb l) z := fun z => by
    rw [← (inclWA l).commutes z, padicInt_hom_ext_pt (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) z]; rfl
  refine ⟨?_, ?_, ?_⟩
  · apply map_inj (inclW l) inclW_injective
    have e1 : (Y.map WittVector.frobenius).map (inclW l) = (Y.map (inclW l)).map (frobW l) := by
      ext i j; simp [frobW_inclW]
    rw [e1, Matrix.map_mul, hY]
    have e2 : (F.A.map bk.ev).map (inclW l) = F.A.map bk.evW := by ext i j; simp [hev]
    rw [e2, Matrix.smul_mul, ← F.φ]
    have e3 : ((inclW l τ ^ N) • F.T).map (frobW l) = frobW l (inclW l τ) ^ N • F.T.map (frobW l) := by
      ext i j; simp
    rw [e3, frobW_inclW, hτ.1, map_mul, hev, smul_smul, mul_pow, mul_comm]
  · intro g
    apply map_inj (inclW l) inclW_injective
    have e1 : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
      ext i j; simp [galW_inclW]
    have e2 : ((ρ g).map (Per.zA l)).map (inclW l) = zW (ρ g) := by ext i j; simp [hz]
    rw [map_smul_rh, map_smul_rh, Matrix.map_mul, Matrix.map_mul, e1, e2, hY]
    have e3 : ((inclW l τ ^ N) • F.T).map (galW l (g : GQ l)) =
        galW l (g : GQ l) (inclW l τ) ^ N • F.T.map (galW l (g : GQ l)) := by
      ext i j; simp
    rw [e3, galW_inclW, Matrix.mul_smul, F.gal, map_pow, map_pow, smul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  · intro g
    apply map_inj (inclW l) inclW_injective
    have key := cocycle_frob (frobW l).toRingHom (galW l (g : GQ l)).toRingEquiv.toRingHom
      (fun x => frobW_galW (g : GQ l) x) (bk.evW bk.E) F.T (F.A.map bk.evW) ((F.ε g).map (inclW l)) (zW (ρ g))
      F.unit F.φ (F.gal g) (by ext i j; simp [zW])
    rw [map_smul_rh, map_smul_rh, Matrix.map_mul, Matrix.map_mul, map_pow, map_pow, hev]
    have e1 : (F.A.map (fun s => Per.σA (g : GQ l) (bk.ev s))).map (inclW l) =
        (F.A.map bk.evW).map (galW l (g : GQ l)).toRingEquiv.toRingHom := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply]
      show _ = galW l (g : GQ l) (bk.evW (F.A i j))
      rw [← hev, galW_inclW]
    have e2 : ((F.ε g).map WittVector.frobenius).map (inclW l) = ((F.ε g).map (inclW l)).map (frobW l).toRingHom := by
      ext i j; simp [frobW_inclW]
    have e3 : (F.A.map bk.ev).map (inclW l) = F.A.map bk.evW := by ext i j; simp [hev]
    rw [e1, e2, e3, ← galW_inclW, hev]
    exact key

end GlobalTheory.FrameEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedFCrystalExistsCoordsEveryPrism
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.CoordEx

theorem exists_basis {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) {d : ℕ}
    (e : Module.Basis (Fin d) A M) : ∃ b : Module.Basis (Fin d) B N, ∀ i, b i = u (e i) := by
  let v : M →ₛₗ[f] (Fin d → B) :=
    { toFun := fun x i => f (e.repr x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  let Q : (Fin d → B) →ₗ[B] N := Fintype.linearCombination B fun i => u (e i)
  have hQ : Q.comp S = LinearMap.id := h.hom_ext fun x => by
    rw [LinearMap.comp_apply, hS, LinearMap.id_apply, Fintype.linearCombination_apply]
    conv_rhs => rw [← e.sum_repr x, map_sum]
    exact Finset.sum_congr rfl fun i _ => (u.map_smulₛₗ _ _).symm
  have hv : ∀ i, S (u (e i)) = Pi.single i 1 := fun i => by
    rw [hS]
    ext j
    change f (e.repr (e i) j) = _
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hQ1 : ∀ i, Q (Pi.single i 1) = u (e i) := fun i => by
    simp [Q, Fintype.linearCombination_apply_single]
  have hS' : S.comp Q = LinearMap.id := by
    refine (Pi.basisFun B (Fin d)).ext fun i => ?_
    rw [Pi.basisFun_apply, LinearMap.comp_apply, hQ1, hv, LinearMap.id_apply]
  refine ⟨(Pi.basisFun B (Fin d)).map (LinearEquiv.ofLinear Q S hQ hS'), fun i => ?_⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.ofLinear_apply, hQ1]

theorem equivFun_eq {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : ℕ}
    (b : Module.Basis (Fin d) A M) (y : M) (c : Fin d → A) (h : y = ∑ i, c i • b i) : b.equivFun y = c := by
  rw [h, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e →
    ∀ B : Obj l ↥(OL K), ∃ V : Eval S B (M.M B), IsCoord e V := by
  intro l _ K bk d S M e hF B
  have hb : ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q), ∃ b : Module.Basis (Fin d) Q.A (M.M Q),
      ∀ i, b i = M.tr g (e i) := fun Q g => exists_basis (M.tr_bc g) e
  choose b hb using hb
  have hs : ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (y : M.M Q),
      y = ∑ i, (b Q g).equivFun y i • M.tr g (e i) := fun Q g y => by
    conv_lhs => rw [← (b Q g).sum_equivFun y]
    exact Finset.sum_congr rfl fun i _ => by rw [hb]
  refine ⟨{ fin := M.fin B
            proj := M.proj B
            v := fun {Q} a g => (b Q g).equivFun.toLinearMap.comp (M.tr a)
            bc := fun {Q} a g => (M.tr_bc a).comp_equiv _
            v_ε := fun {Q} a g g' x => ?_
            v_nat := fun {Q Q'} c a g x i => ?_ }, fun {Q} a g x => hs Q g _⟩
  · change (b Q g).equivFun (M.tr a x) = (S.ε g g').mulVec ((b Q g').equivFun (M.tr a x))
    refine equivFun_eq _ _ _ ?_
    refine (hs Q g' (M.tr a x)).trans ?_
    generalize (b Q g').equivFun (M.tr a x) = c
    simp only [hF.tr g g', Finset.smul_sum, smul_smul, hb, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (c j)]
  · change (b Q' (c.comp g)).equivFun (M.tr (c.comp a) x) i = c.f ((b Q g).equivFun (M.tr a x) i)
    refine congrFun (equivFun_eq _ _ (fun i => c.f ((b Q g).equivFun (M.tr a x) i)) ?_) i
    refine (M.tr_comp c a x).trans ((congrArg (M.tr c) (hs Q g (M.tr a x))).trans ?_)
    refine (map_sum (M.tr c) _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
    exact ((M.tr c).map_smulₛₗ _ _).trans
      (congrArg (c.f _ • ·) ((hb Q' (c.comp g) j).trans (M.tr_comp c g (e j))).symm)

end GlobalTheory.BSP.CoordEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusGaloisRelationFrameAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.GalPhi

variable {l : ℕ} [Fact l.Prime]

theorem σA_frobenius (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  apply inclW_injective
  rw [← frobW_inclW, ← galW_inclW, ← galW_inclW, ← frobW_inclW]
  refine WittVector.ext fun n => ?_
  simp [galW, frobW, mapAlgEquivW, mapEquivW, WittVector.map_coeff, frobenius_def]

theorem frobenius_algebraMap (z : ℤ_[l]) :
    WittVector.frobenius (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z := by
  change WittVector.frobenius (zlW l (OCb l) z) = zlW l (OCb l) z
  rw [WittVector.frobenius_eq_map_frobenius]
  simp only [zlW, RingHom.comp_apply]
  refine WittVector.ext fun n => ?_
  simp only [WittVector.map_coeff]
  exact congrArg (fun φ : ZMod l →+* OCb l => φ (((WittVector.equiv l).symm.toRingHom z).coeff n))
    (RingHom.ext_zmod ((frobenius (OCb l) l).comp (ZMod.castHom (dvd_refl l) (OCb l))) (ZMod.castHom (dvd_refl l) (OCb l)))

theorem gal_ainf {K : FinExt l} (bk : BK K) (τ : Ainf l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (hY : Y.map (inclW l) = inclW l τ ^ N • F.T)
    (g : ↥(GK K)) :
    τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) =
      Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) := by
  have hz : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW (ρ g) := by
    refine Matrix.ext fun i j => ?_; exact (inclWA l).commutes _
  have hσ : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
    refine Matrix.ext fun i j => ?_; exact (galW_inclW _ _).symm
  have hT : (Y.map (inclW l)).map (galW l (g : GQ l)) = inclW l (Per.σA (g : GQ l) τ) ^ N • F.T.map (galW l (g : GQ l)) := by
    rw [hY, ← galW_inclW, ← map_pow]
    refine Matrix.ext fun i j => ?_; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  refine Matrix.ext fun i j => ?_
  apply inclW_injective
  have key : (τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l)))).map (inclW l) =
      (Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)).map (inclW l) := by
    rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, Matrix.map_mul,
      hz, hσ, hT, Matrix.mul_smul, F.gal, hY, Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
    simp only [map_pow]
  exact congrFun (congrFun key i) j

end GlobalTheory.GalPhi

open GlobalTheory.GalPhi in

theorem GlobalTheory.GalPhi.galPhi : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), (bk.ev bk.E * τ) ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * (Y.map WittVector.frobenius).map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) (bk.ev bk.E * τ) ^ N • (Y.map WittVector.frobenius * (F.ε g).map WittVector.frobenius) := by
  intro l _ K bk τ hτ N d ρ F Y hY g
  have h := congrArg (fun M => M.map (WittVector.frobenius : Ainf l →+* Ainf l)) (gal_ainf bk τ N d ρ F Y hY g)
  rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, Matrix.map_mul,
    map_pow, map_pow, ← σA_frobenius, hτ.1] at h
  have h1 : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (WittVector.frobenius : Ainf l →+* Ainf l) =
      (ρ g).map (algebraMap ℤ_[l] (Ainf l)) := by
    refine Matrix.ext fun i j => ?_; exact frobenius_algebraMap _
  have h2 : (Y.map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l) =
      (Y.map WittVector.frobenius).map (Per.σA (g : GQ l)) := by
    refine Matrix.ext fun i j => ?_; exact (σA_frobenius _ _).symm
  rw [h1, h2] at h
  exact h

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesPairStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenbergWiles_pair_alt : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (G F Ω) W) (ρ' : Representation Λ (G F Ω) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ τ ∈ Ine (F := F) B, ρ τ = 1 ∧ ρ' τ = 1) → ∀ (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ C : Set (H1 ρ'), (∀ y : Z1 ρ', Submodule.Quotient.mk y ∈ C ↔ (∀ v ∉ S, ∀ τ ∈ Ine (F := F) (A.1 v), y.1 τ = 0) ∧ ∀ v ∈ S, ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupB (fun g : Dec (F := F) (A.1 v) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g.1 m) P x.1 (fun g => y.1 g.1)) → Finite C ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card W ^ InfinitePlace.nrComplexPlaces F = Nat.card C * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  first | exact @GlobalTheory.PairFormula.greenbergWiles_pair | exact GlobalTheory.PairFormula.greenbergWiles_pair | (intros; apply GlobalTheory.PairFormula.greenbergWiles_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadic
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubLoc

theorem sqrtKur_holds (l : ℕ) [Fact l.Prime] : SqrtKur l := fun p hp h4 hne y hy =>
  GlobalTheory.SqrtUnram.sqrt_neg_prime_mem_Kur l p hp h4 (Ne.symm hne) y hy

theorem kw_le_Kur_all : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i) := by
  intro D i hl2 hq hd w hw
  exact kw_le_Kur_of_ne i (UpperTheory.Small.not_dvd_condN D.host (D.nd.lPrime i).out hl2 hq hd) w hw

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTwistMultipliesRootsOfTameLabelsStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labelTwistMultipliesRoots_of_tame_labels : ∀ D : D7, SumRepresentations.tie0 D → IneRep D → LabDepth D → LabGen D → LabChar D := by
  first | exact @main | exact main | (intros; apply main <;> assumption)
end

