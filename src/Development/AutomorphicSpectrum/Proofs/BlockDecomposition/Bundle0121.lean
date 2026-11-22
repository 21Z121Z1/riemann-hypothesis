import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0119
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0101
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0109
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainIndependence
section
open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.TyFin

def chainUnion (m k t : ℕ) : Fin m ⊕ Fin k → Fin m ⊕ Fin k → Prop
  | .inl a, .inl a' => a < a'
  | .inr w, .inr w' => w < w'
  | .inl a, .inr _ => (a : ℕ) ≤ t
  | .inr _, .inl a => t + 1 ≤ (a : ℕ)

theorem chainUnion_isPat (m k t : ℕ) : IsPat (chainUnion m k t) := by
  constructor
  · rintro (a | w) <;> simp [chainUnion]
  · rintro (a | w) (b | v) (c | u) <;> simp only [chainUnion, Fin.lt_def] <;> omega

theorem chainUnion_remove_right (m k t : ℕ) (q : Fin m) (hq : (q : ℕ) = t + 1) :
    (fun i j => chainUnion m k t i j ∧ ¬ (Sum.isRight i = true ∧ j = Sum.inl q)) =
      chainPat m k (t + 1) := by
  funext i j
  apply propext
  rcases i with a | w <;> rcases j with b | v <;>
    simp only [chainUnion, chainPat, Fin.lt_def, Sum.isRight_inl, Sum.isRight_inr, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, Bool.false_eq_true, false_and, and_false, true_and, and_true,
      not_false_eq_true, Fin.ext_iff] <;> omega

theorem chainUnion_remove_left (m k t : ℕ) (p : Fin m) (hp : (p : ℕ) = t) :
    (fun i j => chainUnion m k t i j ∧ ¬ (i = Sum.inl p ∧ Sum.isRight j = true)) =
      chainPat m k t := by
  funext i j
  apply propext
  rcases i with a | w <;> rcases j with b | v <;>
    simp only [chainUnion, chainPat, Fin.lt_def, Sum.isRight_inl, Sum.isRight_inr, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, Bool.false_eq_true, false_and, and_false, true_and, and_true,
      not_false_eq_true, Fin.ext_iff] <;> omega

theorem chain_step (K : Type) [Field K] [Fintype K] [DecidableEq K] (m k t : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin m ⊕ Fin k) K → ℂ) (hψ : ψ₀ ≠ 1) (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g)
    (ht : t + 1 < m) :
    wh (chainPat m k (t + 1)) (chainE K m k) ψ₀ χ = wh (chainPat m k t) (chainE K m k) ψ₀ χ := by
  have hE : ∀ i j, chainE K m k i j ≠ 0 →
      (∃ a b : Fin m, i = Sum.inl a ∧ j = Sum.inl b ∧ (b : ℕ) = a + 1) ∨
      (∃ w v : Fin k, i = Sum.inr w ∧ j = Sum.inr v ∧ (v : ℕ) = w + 1) := by
    rintro (a | w) (b | v) h
    · left
      by_cases hab : (b : ℕ) = a + 1
      · exact ⟨a, b, rfl, rfl, hab⟩
      · simp [chainE, hab] at h
    · simp [chainE] at h
    · simp [chainE] at h
    · right
      by_cases hab : (v : ℕ) = w + 1
      · exact ⟨w, v, rfl, rfl, hab⟩
      · simp [chainE, hab] at h
  have h := GlobalTheory.T.root_exchange' K (Fin m ⊕ Fin k) (chainUnion m k t) (chainE K m k) ψ₀
    (fun x => Sum.isRight x = true) (Sum.inl ⟨t, by omega⟩) (Sum.inl ⟨t + 1, ht⟩) χ
    (chainUnion_isPat m k t) hψ hχ
    (by
      rintro (a | w) hw
      · simp at hw
      · simp [chainUnion])
    (by simp [chainE])
    (by
      intro i j hij
      rcases hE i j hij with ⟨a, b, rfl, rfl, hab⟩ | ⟨w, v, rfl, rfl, hab⟩ <;>
        simp only [chainUnion, Fin.lt_def] <;> omega)
    (by
      rintro (a | w) hw
      · simp at hw
      · simp [chainE])
    (by
      rintro (a | w) (b | v) hw h1 h2
      · simp at hw
      · simp at hw
      · simp only [chainUnion, Fin.lt_def] at h1 h2
        omega
      · rfl)
    (by
      rintro (a | w) (b | v) hw h1 h2
      · simp at hw
      · simp at hw
      · simp only [chainUnion, Fin.lt_def] at h1 h2
        omega
      · rfl)
    (by
      intro i j l hij hjl hil
      rcases hE i l hil with ⟨a, b, rfl, rfl, hab⟩ | ⟨w, v, rfl, rfl, hab⟩
      · rcases j with c | u
        · simp only [chainUnion, Fin.lt_def] at hij hjl
          omega
        · simp only [chainUnion] at hij hjl
          have h1 : (a : ℕ) = t := by omega
          refine ⟨?_, ?_, by simp⟩
          · simp [Fin.ext_iff, h1]
          · simp [Fin.ext_iff]; omega
      · rcases j with c | u
        · simp only [chainUnion] at hij hjl
          omega
        · simp only [chainUnion, Fin.lt_def] at hij hjl
          omega)
  rw [chainUnion_remove_right m k t ⟨t + 1, ht⟩ rfl,
    chainUnion_remove_left m k t ⟨t, by omega⟩ rfl] at h
  exact h

theorem chainIndep : ReciprocityTheory.Ty.Fin.St.ChainIndep := by
  intro K _ _ _ m k t ψ₀ χ hψ hχ ht
  induction t with
  | zero => rfl
  | succ t ih => rw [chain_step K m k t ψ₀ χ hψ hχ ht, ih (by omega)]

end GlobalTheory.CompanionTheory.TyFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompOfCechPt
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CechPts

open CategoryTheory.Limits

variable {Y X : Scheme.{0}} (f : Y ⟶ X)

def baseOf {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) : U ⟶ X :=
  (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)).app (op U) z

def compOf {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) (i : Fin (k + 1)) : U ⟶ Y :=
  (WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i).app (op U) z

theorem compOf_comp {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) (i : Fin (k + 1)) :
    compOf f z i ≫ f = baseOf f z := by
  have e := WidePullback.π_arrow (fun _ : Fin (k + 1) => yoneda.map f) i
  have := congrArg (fun t => t.app (op U) z) e
  exact this

theorem ext_comp {k : ℕ} {U : Scheme.{0}} (z z' : Sx (cech f) k U)
    (hb : baseOf f z = baseOf f z') (hc : ∀ i, compOf f z i = compOf f z' i) : z = z' := by
  apply yonedaEquiv.symm.injective
  apply WidePullback.hom_ext (fun _ : Fin (k + 1) => yoneda.map f)
  · intro i
    have : yonedaEquiv (yonedaEquiv.symm z ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) =
        yonedaEquiv (yonedaEquiv.symm z' ≫ WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) := by
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hc i
    exact yonedaEquiv.injective this
  · have : yonedaEquiv (yonedaEquiv.symm z ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) =
        yonedaEquiv (yonedaEquiv.symm z' ≫ WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) := by
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hb
    exact yonedaEquiv.injective this

theorem baseOf_cechPt {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    baseOf f (cechPt f k x y h) = x := by
  have e := WidePullback.lift_base (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x)
    (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i])
  exact (congrArg (fun t => t.app (op U) (𝟙 U)) e).trans (Category.id_comp x)

theorem compOf_cechPt {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x)
    (i : Fin (k + 1)) : compOf f (cechPt f k x y h) i = y i := by
  have e := WidePullback.lift_π (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x)
    (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i]) i
  exact (congrArg (fun t => t.app (op U) (𝟙 U)) e).trans (Category.id_comp (y i))

theorem baseOf_res {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech f) k U) :
    baseOf f (Sx.res g z) = g ≫ baseOf f z :=
  NatTrans.naturality_apply (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f)) g.op z

theorem compOf_res {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech f) k U) (i : Fin (k + 1)) :
    compOf f (Sx.res g z) i = g ≫ compOf f z i :=
  NatTrans.naturality_apply (WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) i) g.op z

theorem baseOf_along {p k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) :
    baseOf f (Sx.along z θ) = baseOf f z := by
  have e := WidePullback.lift_base (arrows := fun _ : Fin (p + 1) => yoneda.map f)
    (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f))
    (fun i => WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) (θ.toOrderHom i)) (by simp)
  exact congrArg (fun t => t.app (op U) z) e

theorem compOf_along {p k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) (i : Fin (p + 1)) :
    compOf f (Sx.along z θ) i = compOf f z (θ.toOrderHom i) := by
  have e := WidePullback.lift_π (arrows := fun _ : Fin (p + 1) => yoneda.map f)
    (WidePullback.base (fun _ : Fin (k + 1) => yoneda.map f))
    (fun i => WidePullback.π (fun _ : Fin (k + 1) => yoneda.map f) (θ.toOrderHom i)) (by simp) i
  exact congrArg (fun t => t.app (op U) z) e

theorem map_aug {k : ℕ} {U : Scheme.{0}} (z : Sx (cech f) k U) :
    Sx.map (cechAug f) z = baseOf f z := rfl

theorem cechPt_spec : CrystallineSemistableComparison.E.CechPt := by
  intro Y X f k U
  refine ⟨fun z => ⟨baseOf f z, compOf f z, compOf_comp f z, ?_⟩, ?_, ?_⟩
  · exact ext_comp f _ _ (baseOf_cechPt f _ _ _).symm fun i => (compOf_cechPt f _ _ _ i).symm
  · intro x y h x' y' h' e
    funext i
    rw [← compOf_cechPt f x y h i, e, compOf_cechPt]
  · intro x y h
    refine ⟨?_, ?_, ?_⟩
    · rw [map_aug, baseOf_cechPt]
    · intro V g
      apply ext_comp
      · rw [baseOf_res, baseOf_cechPt, baseOf_cechPt]
      · intro i
        rw [compOf_res, compOf_cechPt, compOf_cechPt]
    · intro p θ
      apply ext_comp
      · rw [baseOf_along, baseOf_cechPt, baseOf_cechPt]
      · intro i
        rw [compOf_along, compOf_cechPt, compOf_cechPt]

end GlobalTheory.CompanionTheory.CechPts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConsequenceOfMackey
section
open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.FromMackey

section Gen

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem repIso_of_constituent {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : FDRep ℂ Γ) (ρ : Representation ℂ Γ V) (hτ : Simple τ) (hρ : IsIrr ρ)
    (hc : IsConstituent τ ρ) : RepIso τ.ρ ρ := by
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have hS : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := GlobalTheory.CompanionTheory.TyFin.simpleIffIrr
  obtain ⟨φ, hφ, hne⟩ := hc
  have hpos : 0 < Module.finrank ℂ (Intw τ.ρ ρ) :=
    Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨φ, hφ⟩, fun h => hne (congrArg Subtype.val h)⟩
  exact hM.2.2.2 Γ _ _ τ.ρ ρ ((hS.1 Γ τ).1 hτ) hρ hpos.ne'

theorem iso_of_repIso {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ τ' : FDRep ℂ Γ) (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W)
    (h₁ : RepIso τ.ρ ρ) (h₂ : RepIso ρ σ) (h₃ : RepIso τ'.ρ σ) : Nonempty (τ ≅ τ') := by
  have hS : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := GlobalTheory.CompanionTheory.TyFin.simpleIffIrr
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  obtain ⟨e₃, he₃⟩ := h₃
  refine (hS.2 Γ τ τ').2 ⟨(e₁.trans e₂).trans e₃.symm, fun γ v => ?_⟩
  apply e₃.injective
  simp [he₁, he₂, he₃]

end Gen

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

theorem cuspIso_refl {α : Type} [Fintype α] [DecidableEq α] (lam : FDRep ℂ (GL α K)) :
    CuspIso K lam lam :=
  (GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts) K α α α lam lam lam lam
    (Equiv.refl α) |>.2.2.1 ⟨Iso.refl _⟩

theorem cuspIso_symm {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)} (h : CuspIso K lam mu) : CuspIso K mu lam := by
  obtain ⟨e, -⟩ := id h
  exact ((GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts) K α β β lam lam mu mu e).1 h

theorem cuspIso_trans {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)}
    {nu : FDRep ℂ (GL γ K)} (h : CuspIso K lam mu) (h' : CuspIso K mu nu) : CuspIso K lam nu := by
  obtain ⟨e, -⟩ := id h
  exact ((GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts) K α β γ lam lam mu nu e).2.1 h h'

variable {K}

theorem supportUnique (hMk : MackeyCusp K) : SupportUnique K := by
  intro n s s' b b' lam mu τ hτ hl hm
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have h := hM.2.1 (GL (Fin n) K) τ _ _ (hcRep K b lam) (hcRep K b' mu) hτ hl.2.2 hm.2.2
  rw [hMk n s s' b b' lam mu hl.1 hm.1 hl.2.1 hm.2.1] at h
  obtain ⟨⟨π, hπ⟩⟩ := (Nat.card_ne_zero.1 h).1
  exact ⟨π, hπ⟩

theorem sqfreeIrr (hMk : MackeyCusp K) : SqfreeIrr K := by
  intro n s b lam hb hl hd
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have hcard := hMk n s s b b lam lam hb hb hl hl
  haveI : Unique {π : Fin s ≃ Fin s // ∀ c, CuspIso K (lam c) (lam (π c))} :=
    { default := ⟨Equiv.refl _, fun c => cuspIso_refl K (lam c)⟩
      uniq := fun ⟨π, h⟩ => Subtype.ext (Equiv.ext fun c => (hd c (π c) (h c)).symm) }
  rw [Nat.card_unique] at hcard
  exact hM.2.2.1 (GL (Fin n) K) _ (hcRep K b lam) hcard

theorem sqfreeUnique (hMk : MackeyCusp K) : SqfreeUnique K := by
  intro n s s' b b' lam mu τ τ' hτ hτ' hl hm hd ⟨π, hπ⟩
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have hd' : ∀ c c', CuspIso K (mu c) (mu c') → c = c' := by
    intro c c' h
    obtain ⟨d, rfl⟩ := π.surjective c
    obtain ⟨d', rfl⟩ := π.surjective c'
    exact congrArg π
      (hd d d' (cuspIso_trans K (hπ d) (cuspIso_trans K h (cuspIso_symm K (hπ d')))))
  have hI : IsIrr (hcRep K b lam) := sqfreeIrr hMk n s b lam hl.1 hl.2.1 hd
  have hI' : IsIrr (hcRep K b' mu) := sqfreeIrr hMk n s' b' mu hm.1 hm.2.1 hd'
  have hne : Module.finrank ℂ (Intw (hcRep K b lam) (hcRep K b' mu)) ≠ 0 := by
    rw [hMk n s s' b b' lam mu hl.1 hm.1 hl.2.1 hm.2.1]
    haveI : Nonempty {π : Fin s ≃ Fin s' // ∀ c, CuspIso K (lam c) (mu (π c))} := ⟨⟨π, hπ⟩⟩
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  exact iso_of_repIso τ τ' (hcRep K b lam) (hcRep K b' mu)
    (repIso_of_constituent τ _ hτ hI hl.2.2)
    (hM.2.2.2 (GL (Fin n) K) _ _ _ _ hI hI' hne)
    (repIso_of_constituent τ' _ hτ' hI' hm.2.2)

theorem fromMackey : ReciprocityTheory.Ty.Fin.St.FromMackey :=
  fun _ _ _ _ hMk => ⟨supportUnique hMk, sqfreeIrr hMk, sqfreeUnique hMk⟩

end GlobalTheory.CompanionTheory.TyFin.FromMackey
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCochainFiltrationDecomposition
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GrpMain

section
variable {R : Type} [CommRing R] {G : Type} [TopologicalSpace G] [AddCommGroup G]
  {M : Type w} [AddCommGroup M] [Module R M]

omit [TopologicalSpace G] in
theorem rho_comm (ρ : Multiplicative G →* (M →ₗ[R] M)) (g h : G) (x : M) :
    ρ (Multiplicative.ofAdd g) (ρ (Multiplicative.ofAdd h) x) =
      ρ (Multiplicative.ofAdd h) (ρ (Multiplicative.ofAdd g) x) := by
  rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

def shiftBy [IsTopologicalAddGroup G] (v : G) (n : ℕ) : C(Fin (n + 1) → G, Fin (n + 1) → G) :=
  ⟨fun x j => x j - v, by fun_prop⟩

def tw [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (v : G) (n : ℕ) :
    (lcCos R G M).cx.X n →ₗ[R] (lcCos R G M).cx.X n where
  toFun f := LocallyConstant.map (ρ (Multiplicative.ofAdd v))
    (LocallyConstant.comap (shiftBy v n) f) - f
  map_add' f g := by
    refine LocallyConstant.ext fun x => ?_
    change ρ (Multiplicative.ofAdd v) (f _ + g _) - (f x + g x) =
      (ρ (Multiplicative.ofAdd v) (f _) - f x) + (ρ (Multiplicative.ofAdd v) (g _) - g x)
    rw [map_add]
    abel
  map_smul' c f := by
    refine LocallyConstant.ext fun x => ?_
    change ρ (Multiplicative.ofAdd v) (c • f _) - c • f x =
      c • (ρ (Multiplicative.ofAdd v) (f _) - f x)
    rw [map_smul, smul_sub]

theorem tw_apply [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (v : G) (n : ℕ)
    (f : (lcCos R G M).cx.X n) (x : Fin (n + 1) → G) :
    tw ρ v n f x = ρ (Multiplicative.ofAdd v) (f fun j => x j - v) - f x := rfl

theorem tw_mem [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (v : G)
    (n : ℕ) (f : (lcCos R G M).cx.X n) (hf : f ∈ eqv ρ S n) : tw ρ v n f ∈ eqv ρ S n := by
  intro g hg x
  have e : (fun j => (fun i => g + x i) j - v) = fun i => g + (fun j => x j - v) i := by
    funext i
    exact add_sub_assoc _ _ _
  rw [tw_apply, tw_apply, e, hf g hg, hf g hg, map_sub, rho_comm]

theorem tw_d [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (v : G) (n : ℕ)
    (f : (lcCos R G M).cx.X n) :
    (lcCos R G M).d n (tw ρ v n f) = tw ρ v (n + 1) ((lcCos R G M).d n f) := by
  refine LocallyConstant.ext fun x => ?_
  rw [tw_apply, lc_d_apply, lc_d_apply, lc_d_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tw_apply, map_zsmul, smul_sub]

def twHom [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (v : G) :
    Cx.Hom (grpCx ρ S) (grpCx ρ S) (RingHom.id R) where
  f n := (tw ρ v n).restrict fun f hf => tw_mem ρ S v n f hf
  comm n x := Subtype.ext (tw_d ρ v n x.1)

def Res (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (D : Submodule R M) (t : R) : Prop :=
  (∀ y ∈ eqv ρ S 0, (lcCos R G M).d 0 y = 0 → ∃ x ∈ D, t • y = LocallyConstant.const _ x) ∧
  ∀ n, ∀ y ∈ eqv ρ S (n + 1), (lcCos R G M).d (n + 1) y = 0 →
    ∃ x ∈ eqv ρ S n, (lcCos R G M).d n x = t • y

def invS (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) : Submodule R M where
  carrier := {x | ∀ g ∈ S, ρ (Multiplicative.ofAdd g) x = x}
  add_mem' {a b} ha hb g hg := by rw [map_add, ha g hg, hb g hg]
  zero_mem' g _ := map_zero _
  smul_mem' c a ha g hg := by rw [map_smul, ha g hg]

def invB (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (v : G) : invS ρ S →ₗ[R] invS ρ S :=
  (ρ (Multiplicative.ofAdd v) - LinearMap.id).restrict fun x hx g hg => by
    change ρ (Multiplicative.ofAdd g) (ρ (Multiplicative.ofAdd v) x - x) =
      ρ (Multiplicative.ofAdd v) x - x
    rw [map_sub, rho_comm, hx g hg]

theorem Res.congr (ρ : Multiplicative G →* (M →ₗ[R] M)) {S S' : Set G} (D : Submodule R M) (t : R)
    (h : ∀ n, eqv ρ S n = eqv ρ S' n) (hr : Res ρ S D t) : Res ρ S' D t := by
  have e : eqv ρ S = eqv ρ S' := funext h
  unfold Res at hr ⊢
  rw [← e]
  exact hr

end

def expo (i : ℕ) : ℕ := 2 ^ i - 1

def idx {k : ℕ} (e : Fin k ≃ Fin k) (i : ℕ) : Set (Fin k) := {j | ∃ a : Fin k, (a : ℕ) < i ∧ e a = j}

abbrev gens (l : ℕ) [Fact l.Prime] {k : ℕ} (e : Fin k ≃ Fin k) (i : ℕ) : Set (Fin k → ℤ_[l]) :=
  (fun j => Pi.single j (1 : ℤ_[l])) '' idx e i

end GlobalTheory.CompanionTheory.GrpMain
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeUniqOf
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeClass

theorem edgeUniq_of : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StAdd → CrystallineSemistableComparison.E.StUniq → CrystallineSemistableComparison.E.EdgeUniq := by
  intro _ hadd huniq R _ C _ F T hG j x x' h h' hx hx'
  obtain ⟨z, hz, st, rfl⟩ := hx
  obtain ⟨z', hz', st', rfl⟩ := hx'
  refine ⟨⟨z + z', ?_, (hadd R C F T j z z' j 0 x x' st st').1, ?_⟩, ?_⟩
  · rw [map_add, hz, hz', add_zero]
  · rfl
  · intro hv
    have st2 : T.St (z - z') j 0 (x - x') := (hadd R C F T j z z' j 0 x x' st st').2
    have hB : z - z' ∈ (cx F).B j := by
      cases j with
      | zero => exact huniq R C F T hG 0 (z - z') 0 0 (x - x') st2 hv
      | succ s =>
        obtain ⟨b, hb, hbx⟩ := hv
        obtain ⟨a, hax, sta⟩ := st2
        refine huniq R C F T hG (s + 1) (z - z') s 1 _ sta ?_
        refine ⟨a - b, ?_, ?_⟩
        · rw [map_sub, hax, hbx, sub_self]
        · rw [map_sub, hb, sub_zero, pow_zero, one_smul]
    exact (Submodule.Quotient.eq _).2 hB

end GlobalTheory.CompanionTheory.EdgeClass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDualInjectiveEquiv
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.ZModDual

private theorem finite_dual_zmod_and_card_le (n : ℕ) [NeZero n] (X : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] :
    Finite (Module.Dual (ZMod n) X) ∧ Nat.card (Module.Dual (ZMod n) X) ≤ Nat.card X := by
  have hfin : Finite (Module.Dual (ZMod n) X) :=
    Finite.of_injective (fun φ : Module.Dual (ZMod n) X => (φ : X → ZMod n)) DFunLike.coe_injective
  refine ⟨hfin, ?_⟩
  letI := Fintype.ofFinite X
  let e : Module.Dual (ZMod n) X → AddChar X ℂ :=
    fun φ => (ZMod.stdAddChar (N := n)).compAddMonoidHom φ.toAddMonoidHom
  have he : Function.Injective e := by
    intro φ ψ h
    ext x
    have hx := DFunLike.congr_fun h x
    exact ZMod.injective_stdAddChar hx
  calc Nat.card (Module.Dual (ZMod n) X) ≤ Nat.card (AddChar X ℂ) :=
        Nat.card_le_card_of_injective e he
    _ = Nat.card X := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

theorem equiv_dual_of_injective_pair :
    ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X]
      [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y],
      (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) →
      (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) →
      Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by
  intro n _ X Y _ _ _ _ _ _ hf hg
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  obtain ⟨hXf, hXc⟩ := finite_dual_zmod_and_card_le n X
  obtain ⟨hYf, hYc⟩ := finite_dual_zmod_and_card_le n Y
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 := Nat.card_le_card_of_injective g hg
  have hXY : Nat.card X = Nat.card Y := by omega
  refine ⟨⟨LinearEquiv.ofBijective f ⟨hf, ?_⟩⟩, hXY⟩
  exact (hf.bijective_of_nat_card_le (by omega)).2

end GlobalTheory.CompanionTheory.ZModDual
end

