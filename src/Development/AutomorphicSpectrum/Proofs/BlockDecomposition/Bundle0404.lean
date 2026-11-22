import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0380
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0381
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0392
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0370
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0393
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0238
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReorderOfUnlinkedCommuteSwap
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSegReorder

theorem exists_minimal_pair {h : ℕ} (R : Fin h → Fin h → Prop) (hex : ∃ a b, a < b ∧ R a b) :
    ∃ a b, a < b ∧ R a b ∧ ∀ c, a < c → c < b → ¬ R c b := by
  classical
  have ex : ∃ d : ℕ, ∃ a b : Fin h, a < b ∧ R a b ∧ b.1 - a.1 = d := by
    obtain ⟨a, b, hab, hR⟩ := hex
    exact ⟨_, a, b, hab, hR, rfl⟩
  obtain ⟨d, ⟨a, b, hab, hR, hd⟩, hmin⟩ :
      ∃ d : ℕ, (∃ a b : Fin h, a < b ∧ R a b ∧ b.1 - a.1 = d) ∧
        ∀ m < d, ¬ ∃ a b : Fin h, a < b ∧ R a b ∧ b.1 - a.1 = m :=
    ⟨Nat.find ex, Nat.find_spec ex, fun m hm => Nat.find_min ex hm⟩
  refine ⟨a, b, hab, hR, fun c hac hcb hc => hmin (b.1 - c.1) ?_ ⟨c, b, hcb, hc, rfl⟩⟩
  have h1 : a.1 < c.1 := hac
  have h2 : c.1 < b.1 := hcb
  omega

theorem arith_step {a b t h : ℕ} (ht : a + (t + 1) < b) (hb : b < h) :
    b - (t + 1) + 1 < h ∧ b - (t + 1) + 1 = b - t ∧ b - (t + 1) < b - t ∧ a < b - (t + 1) ∧ b - (t + 1) < b ∧ a + t < b := by
  omega

theorem arith_end {a b h : ℕ} (hab : a < b) (hb : b < h) :
    a + (b - a - 1) < b ∧ a + 1 < h ∧ b - (b - a - 1) = a + 1 ∧ a < b - (b - a - 1) := by
  omega

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_pair {h : ℕ} (Δ : Fin h → Segment k) (hord : ∀ i j, i < j → ¬ (Δ i).Precedes (Δ j))
    (hlk : ∃ i j, (Δ i).Linked (Δ j)) :
    ∃ a b : Fin h, a < b ∧ (Δ b).Precedes (Δ a) ∧ ∀ c, a < c → c < b → ¬ (Δ c).Linked (Δ b) := by
  obtain ⟨i, j, hij⟩ := hlk
  have hne : i ≠ j := fun e => Segment.not_linked_self (Δ j) (e ▸ hij)
  have ex : ∃ a b : Fin h, a < b ∧ (Δ a).Linked (Δ b) := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, j, hlt, hij⟩
    · exact ⟨j, i, hlt, hij.symm⟩
  obtain ⟨a, b, hab, hlink, hmin⟩ := exists_minimal_pair (fun a b => (Δ a).Linked (Δ b)) ex
  exact ⟨a, b, hab, (Segment.linked_iff_precedes.1 hlink).resolve_left (hord a b hab), hmin⟩

theorem ntrans {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    {G : Type} [Monoid G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    (a : Nonempty (ρ.Equiv σ)) (b : Nonempty (σ.Equiv τ)) : Nonempty (ρ.Equiv τ) := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  exact ⟨a.trans b⟩

theorem equiv_of_eq {h N : ℕ} {y y' : Fin h → IrrGL k} (e : y = y') (hy : ∑ a, (y a).1 = N)
    (hy' : ∑ a, (y' a).1 = N) : Nonempty ((prodIrr y hy).Equiv (prodIrr y' hy')) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem segment_swap_unlinked_adjacent (hcomm : GlobalTheory.BZSeg.LUnlinkedComm k) (hswap : GlobalTheory.BZSeg.SwapProd k) {h N : ℕ} (D : Fin h → Segment k)
    (y : Fin h → IrrGL k) (hy : ∑ a, (y a).1 = N) (hL : ∀ i, IsLSeg (D i) (y i).rep)
    (j : ℕ) (hj : j + 1 < h) (p : j < h) (hu : ¬ (D ⟨j, p⟩).Linked (D ⟨j + 1, hj⟩))
    (hd' : ∑ a, (y (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a)).1 = N) (M : ℕ)
    (hd2 : ∑ a, (![y ⟨j, p⟩, y ⟨j + 1, hj⟩] a).1 = M) (hd2' : ∑ a, (![y ⟨j + 1, hj⟩, y ⟨j, p⟩] a).1 = M) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr (fun a => y (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a)) hd')) :=
  hswap h N y hy j hj M hd2 hd2' hd'
    (hcomm (D ⟨j, p⟩) (D ⟨j + 1, hj⟩) (y ⟨j, p⟩) (y ⟨j + 1, hj⟩) M hd2 hd2' hu (hL ⟨j, p⟩) (hL ⟨j + 1, hj⟩))

theorem step0 (hcomm : GlobalTheory.BZSeg.LUnlinkedComm k) (hswap : GlobalTheory.BZSeg.SwapProd k) {h N : ℕ} (D : Fin h → Segment k)
    (y : Fin h → IrrGL k) (hy : ∑ a, (y a).1 = N) (hL : ∀ i, IsLSeg (D i) (y i).rep)
    (j : ℕ) (hj : j + 1 < h) (p : j < h) (hu : ¬ (D ⟨j, p⟩).Linked (D ⟨j + 1, hj⟩))
    (hd' : ∑ a, (y (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a)).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr (fun a => y (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a)) hd')) :=
  segment_swap_unlinked_adjacent hcomm hswap D y hy hL j hj p hu hd' _ rfl (by simp [Fin.sum_univ_two, add_comm])

def Reach {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (σ : Equiv.Perm (Fin h)) : Prop :=
  ∀ hd' : ∑ a, (x (σ a)).1 = N, Nonempty ((prodIrr x hd).Equiv (prodIrr (x ∘ σ) hd'))

theorem step (hcomm : GlobalTheory.BZSeg.LUnlinkedComm k) (hswap : GlobalTheory.BZSeg.SwapProd k) {h N : ℕ} {Δ : Fin h → Segment k}
    {x : Fin h → IrrGL k} (hd : ∑ a, (x a).1 = N) (hL : ∀ i, IsLSeg (Δ i) (x i).rep) (σ : Equiv.Perm (Fin h))
    (hσ : Reach x hd σ) (j : ℕ) (hj : j + 1 < h) (p : j < h)
    (hu : ¬ (Δ (σ ⟨j, p⟩)).Linked (Δ (σ ⟨j + 1, hj⟩))) :
    Reach x hd (σ * Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩) := by
  intro hd'
  have h1 : ∑ a, (x (σ a)).1 = N := (Equiv.sum_comp σ (fun a => (x a).1)).trans hd
  have h2 : ∑ a, (x (σ (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a))).1 = N :=
    (Equiv.sum_comp (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩) (fun a => (x (σ a)).1)).trans h1
  have F := step0 hcomm hswap (fun a => Δ (σ a)) (fun a => x (σ a)) h1 (fun i => hL (σ i)) j hj p hu h2
  have G := equiv_of_eq (N := N) (y := fun a => x (σ (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a)))
    (y' := x ∘ ⇑(σ * Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩)) rfl h2 hd'
  have E := equiv_of_eq (N := N) (y := x ∘ σ) (y' := fun a => x (σ a)) rfl h1 h1
  exact ntrans (ntrans (ntrans (hσ h1) E) F) G

theorem descend (hcomm : GlobalTheory.BZSeg.LUnlinkedComm k) (hswap : GlobalTheory.BZSeg.SwapProd k) {h N : ℕ} {Δ : Fin h → Segment k}
    {x : Fin h → IrrGL k} (hd : ∑ a, (x a).1 = N) (hL : ∀ i, IsLSeg (Δ i) (x i).rep) (a b : ℕ) (hb : b < h)
    (hun : ∀ (c : ℕ) (hc : c < h), a < c → c < b → ¬ (Δ ⟨c, hc⟩).Linked (Δ ⟨b, hb⟩))
    (t : ℕ) (ht : a + t < b) :
    ∃ σ : Equiv.Perm (Fin h), Reach x hd σ ∧
      σ ⟨b - t, lt_of_le_of_lt (Nat.sub_le b t) hb⟩ = ⟨b, hb⟩ ∧ ∀ i : Fin h, i.1 < b - t → σ i = i := by
  induction t with
  | zero => exact ⟨1, fun hd' => equiv_of_eq rfl hd hd', rfl, fun _ _ => rfl⟩
  | succ t ih =>
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := arith_step ht hb
    obtain ⟨σ, hE, hp, hfix⟩ := ih q6
    have e1 : (⟨b - (t + 1) + 1, q1⟩ : Fin h) = ⟨b - t, lt_of_le_of_lt (Nat.sub_le b t) hb⟩ := Fin.ext q2
    have s0 : σ ⟨b - (t + 1), Nat.lt_of_succ_lt q1⟩ = ⟨b - (t + 1), Nat.lt_of_succ_lt q1⟩ := hfix _ q3
    have s1 : σ ⟨b - (t + 1) + 1, q1⟩ = ⟨b, hb⟩ := by rw [e1]; exact hp
    refine ⟨σ * Equiv.swap (⟨b - (t + 1), Nat.lt_of_succ_lt q1⟩ : Fin h) ⟨b - (t + 1) + 1, q1⟩, ?_, ?_, ?_⟩
    · refine step hcomm hswap hd hL σ hE _ q1 _ ?_
      rw [s0, s1]
      exact hun _ _ q4 q5
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, s1]
    · intro i hi
      have n0 : i ≠ ⟨b - (t + 1), Nat.lt_of_succ_lt q1⟩ := fun e => by rw [e] at hi; exact lt_irrefl _ hi
      have n1 : i ≠ ⟨b - (t + 1) + 1, q1⟩ := fun e => by
        rw [e] at hi
        exact absurd hi (Nat.not_lt.2 (Nat.le_succ _))
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne n0 n1]
      exact hfix i (lt_of_lt_of_le hi (Nat.sub_le_sub_left (Nat.le_succ t) b))

theorem segment_reorder_linked_precedes (hcomm : GlobalTheory.BZSeg.LUnlinkedComm k) (hswap : GlobalTheory.BZSeg.SwapProd k) {h N : ℕ} {Δ : Fin h → Segment k}
    {x : Fin h → IrrGL k} (hd : ∑ a, (x a).1 = N) (hL : ∀ i, IsLSeg (Δ i) (x i).rep)
    (hord : ∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)) (hlk : ∃ i j, (Δ i).Linked (Δ j)) :
    ∃ (σ : Equiv.Perm (Fin h)) (j : ℕ) (hj : j + 1 < h) (p : j < h),
      (Δ (σ ⟨j + 1, hj⟩)).Precedes (Δ (σ ⟨j, p⟩)) ∧ Reach x hd σ := by
  obtain ⟨a, b, hab, hpre, hmin⟩ := exists_pair Δ hord hlk
  obtain ⟨q1, q2, q3, q4⟩ := arith_end (show a.1 < b.1 from hab) b.2
  obtain ⟨σ, hE, hp, hfix⟩ := descend hcomm hswap hd hL a.1 b.1 b.2
    (fun c hc h1 h2 => hmin ⟨c, hc⟩ h1 h2) (b.1 - a.1 - 1) q1
  have e1 : (⟨a.1 + 1, q2⟩ : Fin h) = ⟨b.1 - (b.1 - a.1 - 1), lt_of_le_of_lt (Nat.sub_le _ _) b.2⟩ := Fin.ext q3.symm
  have s0 : σ ⟨a.1, Nat.lt_of_succ_lt q2⟩ = a := hfix a q4
  have s1 : σ ⟨a.1 + 1, q2⟩ = b := by rw [e1]; exact hp
  refine ⟨σ, a.1, q2, Nat.lt_of_succ_lt q2, ?_, hE⟩
  rw [s0, s1]
  exact hpre

theorem reorder : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.LUnlinkedComm k → GlobalTheory.BZSeg.SwapProd k → GlobalTheory.BZSeg.Reorder k :=
  fun _ _ _ _ _ hcomm hswap _ _ _ _ hd hL hord hlk =>
    (segment_reorder_linked_precedes hcomm hswap hd hL hord hlk).elim fun σ H => H.elim fun j H => H.elim fun hj H => H.elim fun _ H =>
      ⟨σ, j, hj, H.1, H.2⟩

end GlobalTheory.CompanionTheory.BZSegReorder
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignOne
section
noncomputable section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.SignLine

theorem signOne : PositivityTheory.RgBcC.RealD.SignOne := by
  intro V _ _ S A hA hS h1
  haveI : FiniteDimensional ℂ S := Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  set B : S →ₗ[ℂ] S := A.restrict hS with hBdef
  obtain ⟨c, hc⟩ := hv (B v)
  have hBw : ∀ w : S, B w = c • w := by
    intro w
    obtain ⟨d, rfl⟩ := hv w
    rw [map_smul, ← hc, smul_comm]
  have hcc : c * c = 1 := by
    have h2 : B (B v) = v := by
      apply Subtype.ext
      show A (A (v : V)) = v
      have := congrArg (fun f : V →ₗ[ℂ] V => f v) hA
      simpa using this
    rw [hBw (B v), hBw v, smul_smul] at h2
    have h3 : (c * c - 1) • v = 0 := by rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  refine ⟨c, mul_self_eq_one_iff.mp hcc, ?_⟩
  have hB : B = c • LinearMap.id := LinearMap.ext fun w => by rw [hBw]; rfl
  rw [trOn, dif_pos hS]
  change LinearMap.trace ℂ S B = c
  rw [hB, map_smul, LinearMap.trace_id]
  simp [h1]

end GlobalTheory.CompanionTheory.SignLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeInvariance
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil

theorem JR_sim {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (γ : GL (Fin M) E) (l : F)
    (hγ : cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J) :
    cT (sigR R σ) ((bc (inclR R) γ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        ((bc (inclR R) γ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (algebraMap R (R ⊗[F] E) (algebraMap F R l)) • JR R J := by
  rw [← GlobalTheory.CompanionTheory.SW.HIsom.JR_conj, hγ]
  ext i j
  change inclR R (algebraMap F E l * J i j) = algebraMap R (R ⊗[F] E) (algebraMap F R l) * inclR R (J i j)
  rw [map_mul]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l

theorem simil : PositivityTheory.Rg.Mass.Simil := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ _ hli hlam hμ h𝓕 hmi hm β β' hβ hβ' hs hs' c hc
  have hl0 : β' / β ≠ 0 := div_ne_zero hβ' hβ
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.similitude_between_nonempty_spheres F E σ hcm J hJ β β' hβ hβ' hs hs'
  obtain ⟨μ', 𝓕', hμ', h𝓕', hth⟩ := GlobalTheory.T.theta_measure_similitude F E σ hcm 2 J hJ μ 𝓕 hμ h𝓕 γ (β' / β) hl0 hγ
  have hT : (fun _ _ => algebraMap F E β' : Matrix (Fin 1) (Fin 1) E) =
      (algebraMap F E (β' / β)) • (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) := by
    funext a b'
    change algebraMap F E β' = algebraMap F E (β' / β) * algebraMap F E β
    rw [← map_mul, div_mul_cancel₀ _ hβ]
  have hth1 := hth 1 _ _ hT
  have hind := GlobalTheory.T.theta_measure_independent_choices F E σ hcm 2 J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕' 1 (fun _ _ => algebraMap F E β)
  change (thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β)).map _ = thetaMeas σ J μ 𝓕 (PositivityTheory.Rg.Mass.sph σ J β') at hth1
  change thetaMeas σ J μ 𝓕 (PositivityTheory.Rg.Mass.sph σ J β) = thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β) at hind
  obtain ⟨ai, a, hau, hai, hav⟩ := GlobalTheory.T.haar_modulus_gl_action_product_formula F E σ hcm 1 2 γ
  obtain ⟨ci, cv, hcu, hci, hcv⟩ := GlobalTheory.T.similitude_scaling_hermitian_measure F E σ hcm (β' / β) hl0
  obtain ⟨-, -, -, -, hq, -⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg F ai ci a cv hau hcu
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := SWIsom.haar_of_loc σ hcm (Ainf F) hLi b li hli.1 1 2
  have hWv := fun v => SWIsom.haar_of_loc σ hcm (Fv F v) (hLv v) b (lam v) (hlam v).1 1 2
  have hJR : ∀ (R : Type) [CommRing R] [Algebra F R],
      cT (sigR R σ) ((bc (inclR R) γ : GL (Fin 2) (R ⊗[F] E)) : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) * JR R J *
        ((bc (inclR R) γ : GL (Fin 2) (R ⊗[F] E)) : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) =
        (algebraMap R (R ⊗[F] E) (algebraMap F R (β' / β))) • JR R J := fun R _ _ => JR_sim R σ J γ _ hγ
  have hunit : ∀ (R : Type) [CommRing R] [Algebra F R] [Nontrivial R], IsUnit (algebraMap F R (β' / β)) :=
    fun R _ _ _ => (IsUnit.mk0 _ hl0).map _
  have sInf := GlobalTheory.T.gram_fibre_measure_local F E σ hcm 2 J hJ (Ainf F) hLi 1 _ _ mi hWi.1 hWi.2 hmi _ _ (hunit _) (hJR _) ai ci
    (hai _ hWi.1) (hci _ hWi.2)
  have sV := fun v => GlobalTheory.T.gram_fibre_measure_local F E σ hcm 2 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v) _ _ (hunit _)
    (hJR _) (a v) (cv v) (hav v _ (hWv v).1) (hcv v _ (hWv v).2)
  have hS : ∀ (R : Type) [CommRing R] [Algebra F R], scalH R σ (algebraMap F R (β' / β))
      (hermScal R σ (algebraMap F R β)) = hermScal R σ (algebraMap F R β') := fun R _ _ => by
    rw [scalH_hermScal, ← map_mul, div_mul_cancel₀ _ hβ]
  have hproj : ∀ X : Fin 1 → Fin 2 → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) γ) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) γ) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) γ) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) γ) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact SWIsom.map_actTup (fstA F) γ X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) γ) X) =
          actTup (Af F) (bc (inclR (Af F)) γ) (projFin X) := by
        funext a i
        exact SWIsom.map_actTup (sndA F) γ X a i
      rw [h1]
      funext a i
      exact SWIsom.map_actTup (evalV F v) γ (projFin X) a i
  have hfin : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β')) (latV b v) < ⊤ := by
    intro v
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermScal (Fv F v) σ (algebraMap F _ β'))).1
    exact ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v).1.measure_lt_top
  have key := euler_move_c F E σ hcm d b 1 2 (thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β)) (mi (hermScal (Ainf F) σ (algebraMap F _ β)))
    (mi (hermScal (Ainf F) σ (algebraMap F _ β')))
    (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β)))
    (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β')))
    (actTup (AF F) (bc (inclR (AF F)) γ))
    (actTup (Ainf F) (bc (inclR (Ainf F)) γ)) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) γ))
    (SWIsom.measurable_actTup σ hcm (AF F) _) (SWIsom.measurable_of_loc σ hcm (Ainf F) hLi _)
    (fun v => SWIsom.measurable_of_loc σ hcm (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hcm d b 1 2).2.1 γ) (ai / ci) (fun v => a v / cv v) hq
    (by rw [sInf, hS]) (fun v => by rw [sV v, hS]) hfin c
  unfold PositivityTheory.Rg.Mass.EP at hc ⊢
  rw [hind] at hc
  rw [← hth1]
  exact key hc

end GlobalTheory.CompanionTheory.SW.MassSimil

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothOperatorFacts
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

variable {n : ℕ}

theorem isSec_comb (E : KMod n) (c : ℂ) {f f' : Mat n → E.V} (h : IsSec E f) (h' : IsSec E f') :
    IsSec E (fun y => c • f y + f' y) := by
  intro g hg k
  simp only [h g hg k, h' g hg k, map_add, map_smul]

section

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)

theorem word_est (hAE : AlgEst) (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hC : CalcSteps)
    (h : C₀(ℝ, ℂ)) (hh : ∀ m : ℕ, ∃ h' : C₀(ℝ, ℂ), ∀ y, h' y = (y : ℂ) ^ m * h y) :
    haveI := FiniteDimensional.complete ℂ E.V
    ∀ (Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V) (T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ) (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T),
      (∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f)) →
      ∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ f f' : Mat n → E.V, IsSec E f' → Sob μ f' →
        cls μ f' = F.Φ h (cls μ f) → ‖cls μ (Rw w f')‖ ≤ C * ‖cls μ f‖ := by
  haveI := FiniteDimensional.complete ℂ E.V
  intro Ω T F hΩ w
  obtain ⟨-, -, -, -, hCF, -, -, -, -, -, -, -, hOF, hIb, -⟩ := hC
  choose hm hhm using hh
  obtain ⟨C₁, hC₁⟩ := (GlobalTheory.T.right_word_laplacian_power_bound) n μ E.V hL hU hR hAE hCF hIb w
  obtain ⟨Q, hQ⟩ := (GlobalTheory.T.laplacian_casimir_relation) n E hR hOF
  choose Cj hCj using (GlobalTheory.T.laplacian_power_casimir_bound) n μ E Q hL hU hR hCF hQ
  refine ⟨|C₁| * ∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖, ?_⟩
  intro f f' hsec hS hcl
  have hsob : ∀ i, Sob μ (Om^[i] f') := by
    intro i
    induction i with
    | zero => exact hS
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact GlobalTheory.CompanionTheory.SobOpsPf.sob_Om ih
  have hit : ∀ i, cls μ (Om^[i] f') = F.Φ (hm i) (cls μ f) := by
    intro i
    induction i with
    | zero =>
      have : hm 0 = h := by ext y; simp [hhm]
      simpa [this] using hcl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      have hmem : cls μ (Om^[i] f') ∈ Msob μ E.V := Submodule.subset_span ⟨_, hsob i, rfl⟩
      rw [← hΩ _ hmem (hsob i)]
      exact F.omega (hm i) (hm (i + 1)) (fun y => by simp only [hhm]; ring) _ _ ih
  have hn : ∀ i, ‖cls μ (Om^[i] f')‖ ≤ ‖hm i‖ * ‖cls μ f‖ := by
    intro i
    rw [hit]
    exact ((F.Φ (hm i)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (F.norm_le _) (norm_nonneg _))
  have hj : ∀ j, ‖cls μ (Lap^[j] f')‖ ≤ (|Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
    intro j
    have hs : ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ ≤ (∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => hn i
    have h0 : 0 ≤ ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc _ ≤ Cj j * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ := hCj j f' hS hsec
      _ ≤ |Cj j| * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f')‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |Cj j| * ((∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖) :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = _ := by ring
  have h0 : 0 ≤ ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hs : ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ ≤
      (∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hj j
  calc _ ≤ C₁ * ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ := hC₁ f' hS
    _ ≤ |C₁| * ∑ j ∈ range (w.length + 1), ‖cls μ (Lap^[j] f')‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) h0
    _ ≤ |C₁| * ((∑ j ∈ range (w.length + 1), |Cj j| * ∑ i ∈ range (j + 1), ‖hm i‖) * ‖cls μ f‖) :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = _ := by ring

end

theorem smoothOp : SmoothOp := by
  intro n _ _ μ _ E
  haveI := FiniteDimensional.complete ℂ E.V
  intro Ω T F hL hU hR hS hAE hC hΩ h hh
  have hW := word_est μ E hAE hL hU hR hC h hh Ω T F hΩ
  choose Cw hCw using hW
  obtain ⟨S, Cs, hb⟩ := GlobalTheory.CompanionTheory.CurveJ.sup_bound hS n μ
  have hkeep := (GlobalTheory.T.functional_calculus_on_sobolev) n μ E Ω T F hL hU hR hS hC hΩ h
  refine ⟨|Cs| * ∑ w ∈ S, |Cw w|, fun x hx => ?_⟩
  obtain ⟨xs, hxs, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  choose fs hfS hfsec hfcl using hxs
  choose a haS hasec hacl using fun k => hkeep (fs k) (hfS k) (hfsec k)
  have hacl' : ∀ k, cls μ (a k) = F.Φ h (xs k) := fun k => by rw [hacl, hfcl]

  have hdiff : ∀ w k l, ‖cls μ (Rw w (a k)) - cls μ (Rw w (a l))‖ ≤ |Cw w| * ‖xs k - xs l‖ := by
    intro w k l
    have c1 := GlobalTheory.CompanionTheory.CurveJ.sob_comb (-1) (haS l) (haS k)
    have c2 := GlobalTheory.CompanionTheory.CurveJ.sob_comb (-1) (hfS l) (hfS k)
    have e1 : cls μ (fun y => (-1 : ℂ) • fs l y + fs k y) = xs k - xs l := by
      have := c2.2 []
      simp only [Rw, id] at this
      rw [this, hfcl, hfcl]
      simp [sub_eq_neg_add]
    have e2 : cls μ (fun y => (-1 : ℂ) • a l y + a k y) = F.Φ h (cls μ (fun y => (-1 : ℂ) • fs l y + fs k y)) := by
      have := c1.2 []
      simp only [Rw, id] at this
      rw [this, hacl', hacl', e1, map_sub]
      simp [sub_eq_neg_add]
    have b := hCw w _ _ (isSec_comb E (-1) (hasec l) (hasec k)) c1.1 e2
    rw [c1.2 w, e1] at b
    have e3 : (-1 : ℂ) • cls μ (Rw w (a l)) + cls μ (Rw w (a k)) = cls μ (Rw w (a k)) - cls μ (Rw w (a l)) := by
      simp [sub_eq_neg_add]
    rw [e3] at b
    exact b.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have hcs : CauchySeq xs := hlim.cauchySeq
  have hcau : ∀ w, CauchySeq fun k => cls μ (Rw w (a k)) := by
    intro w
    rw [Metric.cauchySeq_iff] at hcs ⊢
    intro ε hε
    have hpos : 0 < |Cw w| + 1 := by positivity
    obtain ⟨N, hN⟩ := hcs (ε / (|Cw w| + 1)) (div_pos hε hpos)
    refine ⟨N, fun k hk l hl => ?_⟩
    have h1 := hN k hk l hl
    rw [dist_eq_norm] at h1 ⊢
    have h2 := hdiff w k l
    rw [lt_div_iff₀ hpos] at h1
    nlinarith [norm_nonneg (xs k - xs l), abs_nonneg (Cw w)]
  obtain ⟨b, hbS, hbt, hbp⟩ := (GlobalTheory.T.sobolev_space_complete) n μ E.V hS a haS hcau
  refine ⟨b, hbS, ?_, ?_, ?_⟩
  · intro g hg k
    have hgk : g * k.1 ∈ GLs n := by
      have hk : (k.1 : Mat n).det ≠ 0 := by
        intro h0
        have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.1 k.2)
        rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
        exact zero_ne_one this
      show (g * k.1).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero hg hk
    have t1 := hbp _ hgk
    have t2 : Tendsto (fun j => a j (g * k.1)) atTop (𝓝 (E.ρ k⁻¹ (b g))) := by
      simp only [fun j => hasec j g hg k]
      exact ((E.ρ k⁻¹).continuous.tendsto _).comp (hbp g hg)
    exact tendsto_nhds_unique t1 t2
  · have t1 := hbt []
    simp only [Rw, id] at t1
    have t2 : Tendsto (fun k => cls μ (a k)) atTop (𝓝 (F.Φ h x)) := by
      simp only [hacl']
      exact ((F.Φ h).continuous.tendsto _).comp hlim
    exact tendsto_nhds_unique t1 t2
  · have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
    have t1 : Tendsto (fun k => ‖a k 1‖) atTop (𝓝 ‖b 1‖) := (hbp 1 h1).norm
    have t2 : Tendsto (fun k => (|Cs| * ∑ w ∈ S, |Cw w|) * ‖xs k‖) atTop (𝓝 ((|Cs| * ∑ w ∈ S, |Cw w|) * ‖x‖)) :=
      hlim.norm.const_mul _
    refine le_of_tendsto_of_tendsto' t1 t2 fun k => ?_
    have b1 := hb E.V (a k) (haS k) 1 h1
    have h0 : 0 ≤ ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hs : ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ ≤ (∑ w ∈ S, |Cw w|) * ‖xs k‖ := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun w _ => ?_
      have := hCw w (fs k) (a k) (hasec k) (haS k) (by rw [hacl', hfcl])
      rw [hfcl] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    calc _ ≤ Cs * ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := b1
      _ ≤ |Cs| * ∑ w ∈ S, ‖cls μ (Rw w (a k))‖ := mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |Cs| * ((∑ w ∈ S, |Cw w|) * ‖xs k‖) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = _ := by ring

end GlobalTheory.CompanionTheory.FcSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRepIsSmoothFoundationStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_rep_is_smooth_foundation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → GroundTheory.Automorphic.IsSmooth π := by
  first | exact @GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found | exact GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found | (intros; apply GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableUnitarizableStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_integrable_unitarizable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k), IsSqIntCoeff x.rep → IsUnitarisable x.rep := by
  first | exact @GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff | exact GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff | (intros; apply GlobalTheory.CompanionTheory.SqIntUnit.isUnitarisable_of_isSqIntCoeff <;> assumption)
end

