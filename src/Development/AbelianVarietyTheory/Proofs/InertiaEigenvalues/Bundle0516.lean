import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisesEtaleFCrystalPullbackGalois
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialFamilySummandRestriction
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.SummandDual

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isDR_of_summand (D : D7) (hFont : FontaineAtPlacesOverL (D := D)) (hP : PotDRL D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ)
    (hPot : PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n)
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
    (hX : IsSummandTw i w hw r Xs X) : IsDR (Br.PD D.loc D.nbr i w hw) X.ρ := by
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hx⟩ := hPot
  obtain ⟨a, x, j, hjinj, hjeq, -⟩ := hX
  let incl := Subgroup.inclusion (GK_le h)
  have hincl : Continuous incl := Continuous.subtype_mk continuous_subtype_val _
  let W' : GRep ↥(GK K') ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
    { V := X.V, ρ := X.ρ.comp incl, cont := fun v => (X.cont v).comp hincl }
  let Ms' : ↥Xs → (↥(GK K') →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun y => (Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp incl
  have hc' : ∀ y v, Continuous fun g => (Ms' y g).mulVec v := fun y v =>
    ((GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr y).1).comp hincl).matrix_mulVec
      continuous_const
  have hcr' : ∀ y, IsCrys ((D.loc (D.nd.l i)).PD K') (matRep (Ms' y)) := fun y =>
    (GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))).2.1 (hx y).1
  have hsub : IsSubOfSums W'.ρ (fun y => ⇑(Ms' y)) := by
    refine ⟨a, x, j, hjinj, fun g v => ?_⟩
    exact hjeq (incl g) v
  have hW' : IsCrys ((D.loc (D.nd.l i)).PD K') W'.ρ :=
    (subsum_crys (PD := (D.loc (D.nd.l i)).PD K') (Ms := Ms') (hc := hc')
      (hF := hFont (D.nd.l i) K' (D.nbr i w hw).LL) (S := fun _ => Set.univ)
      (hcr := hcr') (hS := fun _ _ _ _ => Set.mem_univ _) (A := W') (hA := hsub)).1
  exact hP (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h X hW'

section Lin

variable {LL : Type} [Field LL] {a n : ℕ}

def pr (LL : Type) [Field LL] (a n : ℕ) :
    (Fin a → Fin n → LL) →ₗ[LL] (Fin a → Fin n → LL) →ₗ[LL] LL :=
  LinearMap.mk₂ LL (fun u u' => ∑ b, u b ⬝ᵥ u' b)
    (fun u₁ u₂ u' => by simp [add_dotProduct, Finset.sum_add_distrib])
    (fun c u u' => by simp [smul_dotProduct, Finset.mul_sum])
    (fun u u₁ u₂ => by simp [dotProduct_add, Finset.sum_add_distrib])
    (fun c u u' => by simp [dotProduct_smul, Finset.mul_sum])

theorem pr_apply (u u' : Fin a → Fin n → LL) : pr LL a n u u' = ∑ b, u b ⬝ᵥ u' b := rfl

def ann (C : Submodule LL (Fin a → Fin n → LL)) : Submodule LL (Fin a → Fin n → LL) where
  carrier := {u' | ∀ u ∈ C, pr LL a n u u' = 0}
  add_mem' := fun h1 h2 u hu => by rw [map_add, h1 u hu, h2 u hu, add_zero]
  zero_mem' := fun u _ => by rw [map_zero]
  smul_mem' := fun c u' h u hu => by rw [map_smul, h u hu, smul_zero]

theorem pr_single (b : Fin a) (k : Fin n) (u' : Fin a → Fin n → LL) :
    pr LL a n (Pi.single b (Pi.single k 1)) u' = u' b k := by
  rw [pr_apply, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

theorem exists_rep (φ : (Fin a → Fin n → LL) →ₗ[LL] LL) :
    ∃ u' : Fin a → Fin n → LL, ∀ u, φ u = pr LL a n u u' := by
  refine ⟨fun b k => φ (Pi.single b (Pi.single k 1)), fun u => ?_⟩
  have hu : u = ∑ b, ∑ k, u b k • (Pi.single b (Pi.single k 1) : Fin a → Fin n → LL) := by
    funext b' k'
    simp [Finset.sum_apply, Pi.single_apply, ite_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']
  conv_lhs => rw [hu]
  rw [pr_apply]
  simp [map_sum, dotProduct]

theorem eq_zero_of_pr (u' : Fin a → Fin n → LL) (h : ∀ u, pr LL a n u u' = 0) : u' = 0 := by
  funext b k
  rw [← pr_single b k u']
  exact h _

end Lin

section Lin2

variable {LL : Type} [Field LL] {a n : ℕ}

theorem left_nondeg (R C : Submodule LL (Fin a → Fin n → LL)) (hRC : IsCompl R C) (u : Fin a → Fin n → LL)
    (hu : u ∈ R) (h : ∀ u' ∈ ann C, pr LL a n u u' = 0) : u = 0 := by
  by_contra hne
  have hne' : (⟨u, hu⟩ : ↥R) ≠ 0 := fun h0 => hne (congrArg Subtype.val h0)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual LL ↥R, f ⟨u, hu⟩ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne' ((Module.forall_dual_apply_eq_zero_iff LL _).1 hall)
  obtain ⟨u', hu'⟩ := exists_rep (f ∘ₗ R.projectionOnto C hRC)
  have hann : u' ∈ ann C := by
    intro c hc
    rw [← hu', LinearMap.comp_apply, Submodule.linearProjOfIsCompl_apply_right' hRC hc, map_zero]
  apply hf
  have := hu' u
  rw [LinearMap.comp_apply, Submodule.linearProjOfIsCompl_apply_left hRC ⟨u, hu⟩] at this
  rw [this]
  exact h u' hann

theorem right_nondeg (R C : Submodule LL (Fin a → Fin n → LL)) (hRC : IsCompl R C) (u' : Fin a → Fin n → LL)
    (hu' : u' ∈ ann C) (h : ∀ u ∈ R, pr LL a n u u' = 0) : u' = 0 := by
  apply eq_zero_of_pr
  intro u
  have hu : u ∈ R ⊔ C := by rw [hRC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
  rw [map_add, LinearMap.add_apply, h y hy, hu' z hz, add_zero]

variable {G : Type} [Group G] (T U : Fin a → (G →* Matrix (Fin n) (Fin n) LL)) (χ : G → LL)

theorem pr_equiv (hU : ∀ b g, U b g = χ g • (T b g⁻¹).transpose) (g : G) (u u' : Fin a → Fin n → LL) :
    pr LL a n (fun b => (T b g).mulVec (u b)) (fun b => (U b g).mulVec (u' b)) = χ g * pr LL a n u u' := by
  rw [pr_apply, pr_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hU, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
    dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
    inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]

theorem ann_stable (hU : ∀ b g, U b g = χ g • (T b g⁻¹).transpose) (C : Submodule LL (Fin a → Fin n → LL))
    (hC : ∀ g, ∀ u ∈ C, (fun b => (T b g).mulVec (u b)) ∈ C) (g : G) (u' : Fin a → Fin n → LL)
    (hu' : u' ∈ ann C) : (fun b => (U b g).mulVec (u' b)) ∈ ann C := by
  intro u hu
  have e : u = fun b => (T b g).mulVec ((T b g⁻¹).mulVec (u b)) := by
    funext b
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  rw [e, pr_equiv T U χ hU, hu' _ (hC g⁻¹ u hu), mul_zero]

end Lin2

theorem finrank_eq_of_perfect {LL : Type} [Field LL] {V V' : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [FiniteDimensional LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL) (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) :
    finrank LL V = finrank LL V' := by
  first
  | exact @_root_.GlobalTheory.NondegenerateFinrank.main
  | exact _root_.GlobalTheory.NondegenerateFinrank.main
  | (apply _root_.GlobalTheory.NondegenerateFinrank.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NondegenerateFinrank.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NondegenerateFinrank.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NondegenerateFinrank.main ..)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem dual_of_summand (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
    (hX : IsSummandTw i w hw r Xs X) :
    ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX ∧
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) X' := by
  obtain ⟨a, x, j, hjinj, hjeq, C, hC, hcompl⟩ := hX
  let Ms : ↥Xs → (Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun y => Br.loc D.nbr i w hw (rDuO D.nd i r y)
  have hc : ∀ y v, Continuous fun g => (Ms y g).mulVec v := fun y v =>
    (GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr y).2).matrix_mulVec continuous_const
  let T : Fin a → (Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun b => Br.loc D.nbr i w hw (rTwO D.nd i r (x b))
  let χ : Br.G D.nbr i w hw → Br.LL D.nbr i w hw := fun g =>
    ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw)
  have hU : ∀ b g, Ms (x b) g = χ g • (T b g⁻¹).transpose := fun b g =>
    GlobalTheory.JumpDual.loc_dual D i w hw r (x b) g
  let A := GRep.sum (Qp := ℚ_[D.nd.l i]) (O := Br.OLL D.nbr i w hw) Ms hc x
  have hstab : ∀ g, ∀ u ∈ ann C, A.ρ g u ∈ ann C := fun g u hu =>
    ann_stable T (fun b => Ms (x b)) χ hU C hC g u hu
  let X' := A.sub (ann C) hstab
  let PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw :=
    (pr (Br.LL D.nbr i w hw) a D.R.nV).compl₁₂ j (ann C).subtype
  have hPX : ∀ v (y : X'.V), PX v y = pr (Br.LL D.nbr i w hw) a D.R.nV (j v) ((ann C).subtype y) :=
    fun _ _ => rfl
  have h2 : ∀ v, (∀ y, PX v y = 0) → v = 0 := by
    intro v h
    apply hjinj
    rw [map_zero]
    exact left_nondeg (LinearMap.range j) C hcompl (j v) ⟨v, rfl⟩ fun u' hu' => h ⟨u', hu'⟩
  have h3 : ∀ y, (∀ v, PX v y = 0) → y = 0 := by
    intro y h
    apply Subtype.ext
    exact right_nondeg (LinearMap.range j) C hcompl y.1 y.2 (by
      rintro u ⟨v, rfl⟩
      exact h v)
  refine ⟨X', PX, ⟨fun g v y => ?_, h2, h3, finrank_eq_of_perfect PX h2 h3⟩, ?_⟩
  · rw [hPX, hPX, hjeq]
    exact pr_equiv T (fun b => Ms (x b)) χ hU g (j v) ((ann C).subtype y)
  · refine ⟨a, x, fun b => LinearMap.proj b ∘ₗ (ann C).subtype, fun b g v => rfl, fun v hv => ?_⟩
    exact Subtype.ext (funext hv)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem xdual : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
      IsDR (Br.PD D.loc D.nbr i w hw) X.ρ ∧
      ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX ∧
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) X' := by
  intro D hFont hP i r hr Xs w hw n hPot X hX
  exact ⟨isDR_of_summand D hFont hP i r hr Xs w hw n hPot X hX, dual_of_summand D i r hr Xs w hw X hX⟩

end GlobalTheory.SummandDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeNatCastNeZeroWittOfTiltFiniteField
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
  GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.Compl

theorem smodEq_span_pow {R : Type} [CommRing R] (r x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {r} ^ n • ⊤ : Submodule R R)] ↔ ∃ z, x - y = r ^ n * z := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨fun ⟨z, hz⟩ => ⟨z, by rw [← hz, mul_comm]⟩, fun ⟨z, hz⟩ => ⟨z, by rw [hz, mul_comm]⟩⟩

theorem natCast_ne_zero_K (l : ℕ) [Fact l.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] {n : ℕ}
    (hn : n ≠ 0) : (n : K) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ_[l] K) n]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type)
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (e : ℕ)

def iota (τ : ZMod a) : Wq l a →+* K := (algebraMap O K).comp (emb t τ).toRingHom

variable {K}

theorem iota_injective (τ : ZMod a) : Function.Injective (iota t K τ) := by
  have := Fintype.ofFinite (Fq l a)
  rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra h0
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  have hu : IsUnit b := WittVector.isUnit_of_coeff_zero_ne_zero b hb
  rw [map_mul, map_pow, map_natCast] at hw
  exact mul_ne_zero (pow_ne_zero _ (natCast_ne_zero_K l (K := K) hl.out.ne_zero)) (hu.map (iota t K τ)).ne_zero hw

include t K in
theorem prime_natCast_ne_zero_wittOfTiltFiniteField : (l : Wq l a) ≠ 0 := fun h => by
  have h1 := congrArg (iota t K 0) h
  rw [map_natCast, map_zero] at h1
  exact natCast_ne_zero_K l (K := K) hl.out.ne_zero h1

variable (K) in

def Rep (F : ZMod a → K⟦X⟧) (w : ℕ → Wq l a) : Prop :=
  ∀ τ n, ((n / e).factorial : K) * coeff n (F τ) = iota t K τ (w n)

variable {t e}

theorem rep_unique {F : ZMod a → K⟦X⟧} {w v : ℕ → Wq l a} (hw : Rep t K e F w) (hv : Rep t K e F v) : w = v :=
  funext fun n => iota_injective t 0 (by rw [← hw 0 n, ← hv 0 n])

theorem eq_of_rep {F G : ZMod a → K⟦X⟧} {w : ℕ → Wq l a} (hF : Rep t K e F w) (hG : Rep t K e G w) : F = G := by
  funext τ
  ext n
  exact mul_left_cancel₀ (natCast_ne_zero_K l (K := K) (Nat.factorial_ne_zero _)) ((hF τ n).trans (hG τ n).symm)

theorem rep_sub {F G : ZMod a → K⟦X⟧} {w v : ℕ → Wq l a} (hF : Rep t K e F w) (hG : Rep t K e G v) :
    Rep t K e (F - G) (w - v) := fun τ n => by
  simp only [Pi.sub_apply, map_sub, mul_sub, hF τ n, hG τ n]

theorem rep_pow_mul (m : ℕ) {F : ZMod a → K⟦X⟧} {w : ℕ → Wq l a} (hF : Rep t K e F w) :
    Rep t K e ((l : ZMod a → K⟦X⟧) ^ m * F) (fun n => (l : Wq l a) ^ m * w n) := fun τ n => by
  have h1 : ((l : ZMod a → K⟦X⟧) ^ m * F) τ = C ((l : K) ^ m) * F τ := by
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, map_pow, map_natCast]
  rw [h1, coeff_C_mul, map_mul, map_pow, map_natCast, ← hF τ n]
  ring

variable (t e) in

def ofRep (w : ℕ → Wq l a) : ZMod a → K⟦X⟧ :=
  fun τ => PowerSeries.mk fun n => iota t K τ (w n) / ((n / e).factorial : K)

theorem rep_ofRep (w : ℕ → Wq l a) : Rep t K e (ofRep (K := K) t e w) w := fun τ n => by
  rw [ofRep, coeff_mk]
  exact mul_div_cancel₀ _ (natCast_ne_zero_K l (K := K) (Nat.factorial_ne_zero _))

variable (t e) in
theorem isHausdorff_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsHausdorff (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  have := Fintype.ofFinite (Fq l a)
  refine ⟨fun x hx => ?_⟩
  obtain ⟨w, -, hw⟩ := hsd x.1 x.2
  have hdiv : ∀ m k, ∃ q, w k = (l : Wq l a) ^ m * q := by
    intro m k
    obtain ⟨z, hz⟩ := (smodEq_span_pow _ _ _ m).1 (hx m)
    rw [sub_zero] at hz
    obtain ⟨v, -, hv⟩ := hsd z.1 z.2
    have h1 : x.1 = (l : ZMod a → K⟦X⟧) ^ m * z.1 := by rw [hz]; push_cast; rfl
    have h2 := rep_pow_mul m hv
    rw [← h1] at h2
    exact ⟨v k, congrFun (rep_unique hw h2) k⟩
  have hw0 : w = 0 := funext fun k => IsHausdorff.haus' (I := Ideal.span {(l : Wq l a)}) (w k) fun m => by
    obtain ⟨q, hq⟩ := hdiv m k
    exact (smodEq_span_pow _ _ _ m).2 ⟨q, by rw [sub_zero, hq]⟩
  apply Subtype.ext
  refine eq_of_rep (F := x.1) (G := 0) hw ?_
  rw [hw0]
  intro τ n
  simp

variable (t e) in
theorem isPrecomplete_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsPrecomplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  have := Fintype.ofFinite (Fq l a)
  refine ⟨fun f hf => ?_⟩
  choose w hw0 hw using fun j => hsd (f j).1 (f j).2
  have hc : ∀ {m j : ℕ}, m ≤ j → ∀ k,
      w m k ≡ w j k [SMOD (Ideal.span {(l : Wq l a)} ^ m • ⊤ : Submodule (Wq l a) (Wq l a))] := by
    intro m j hmj k
    obtain ⟨z, hz⟩ := (smodEq_span_pow _ _ _ m).1 (hf hmj)
    obtain ⟨v, -, hv⟩ := hsd z.1 z.2
    have h1 : (f m).1 - (f j).1 = (l : ZMod a → K⟦X⟧) ^ m * z.1 := by
      have h0 := congrArg Subtype.val hz
      push_cast at h0
      exact h0
    have h2 := rep_pow_mul m hv
    rw [← h1] at h2
    have h3 := congrFun (rep_unique (rep_sub (hw m) (hw j)) h2) k
    exact (smodEq_span_pow _ _ _ m).2 ⟨v k, by simpa using h3⟩
  choose W hW using fun k => IsPrecomplete.prec' (I := Ideal.span {(l : Wq l a)}) (fun j => w j k)
    (fun {m j} h => hc h k)
  have hW0 : LTo0 l W := fun r => (hw0 r r).mono fun k hk => by
    obtain ⟨q, hq⟩ := (smodEq_span_pow _ _ _ r).1 (hW k r)
    have h1 : W k = w r k - (l : Wq l a) ^ r * q := by rw [← hq]; ring
    rw [h1]
    exact dvd_sub hk (dvd_mul_right _ _)
  have hLmem : ofRep (K := K) t e W ∈ Sd t K e := Subring.subset_closure ⟨W, hW0, rep_ofRep W⟩
  refine ⟨⟨_, hLmem⟩, fun n => ?_⟩
  choose v hv using fun k => (smodEq_span_pow _ _ _ n).1 (hW k n)
  have hl0 : (l : Wq l a) ^ n ≠ 0 := pow_ne_zero _ (prime_natCast_ne_zero_wittOfTiltFiniteField t (K := K))
  have hv0 : LTo0 l v := fun r => ((hw0 n (r + n)).and (hW0 (r + n))).mono fun k hk => by
    have h1 : (l : Wq l a) ^ n * (l : Wq l a) ^ r ∣ (l : Wq l a) ^ n * v k := by
      rw [← hv k, ← pow_add, add_comm]
      exact dvd_sub hk.1 hk.2
    exact (mul_dvd_mul_iff_left hl0).1 h1
  have hymem : ofRep (K := K) t e v ∈ Sd t K e := Subring.subset_closure ⟨v, hv0, rep_ofRep v⟩
  refine (smodEq_span_pow _ _ _ n).2 ⟨⟨_, hymem⟩, Subtype.ext ?_⟩
  have h1 := rep_sub (hw n) (rep_ofRep (K := K) (t := t) (e := e) W)
  have h2 := rep_pow_mul n (rep_ofRep (K := K) (t := t) (e := e) v)
  have h3 : (fun k => (l : Wq l a) ^ n * v k) = w n - W := funext fun k => by rw [Pi.sub_apply, hv k]
  rw [h3] at h2
  have h4 := eq_of_rep h1 h2
  push_cast
  exact h4

variable (t e) in

theorem isAdicComplete_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsAdicComplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) :=
  { toIsHausdorff := isHausdorff_of t e hsd, toIsPrecomplete := isPrecomplete_of t e hsd }

end GlobalTheory.CrysPrism.Compl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisesEtaleFCrystalPullbackGaloisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisesEtaleFCrystal_pullback_galois : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (E : FCrys l ↥(OL K)) (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∀ (g : GQ l) (σ : ↥(OL K) →+* ↥(OL K)), (∀ x, (((σ x : ↥K.1) : Om l)) = g ((x : ↥K.1) : Om l)) → (∀ h ∈ GK K, g⁻¹ * h * g ∈ GK K) → ∀ (ρg : T ≃ₗ[ℤ_[l]] T), (∀ h h' : ↥(GK K), (h' : GQ l) = g⁻¹ * h * g → ∀ x, ρg (ρ h' x) = ρ h (ρg x)) → ∃ (gH : Hom (ainfObj K) ((ainfObj K).restrict σ)) (j' : (E.pullback σ).M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), (∀ x, gH.f x = Per.σA g x) ∧ Realises K (E.pullback σ) (ainfObj K) (ainfId K) T ρ j' ∧ ∀ z, j' (E.tr gH z) = TensorProduct.map (galW l g).toLinearMap ρg.toLinearMap (j z) := by
  first | exact @GlobalTheory.Prism.PullGal.realises_pullback | exact GlobalTheory.Prism.PullGal.realises_pullback | (intros; apply GlobalTheory.Prism.PullGal.realises_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBlochKatoLatticeDualOrthogonalStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualBlochKato_lattice_dual_orthogonal : LocalTateDuality → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ (x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) (y : Z1 ((red i K ρ).comp (DecV N v).subtype)), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v → CupCob (fun g : DecV N v => algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i)) ((red i K ρ).comp (DecV N v).subtype) (dotProductBilin K K) x.1 y.1 := by
  first | exact @GlobalTheory.ResOrth.bkOn_orthogonal | exact GlobalTheory.ResOrth.bkOn_orthogonal | (intros; apply GlobalTheory.ResOrth.bkOn_orthogonal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExtStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_crystalline_deRham_finiteExt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (IsCrys (P.PD K) ρ → IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) ∧ (IsDR (P.PD K) ρ ↔ IsDR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) := by
  first | exact @GlobalTheory.Per.TiedRestrict.restrict_crys_deRham | exact GlobalTheory.Per.TiedRestrict.restrict_crys_deRham | (intros; apply GlobalTheory.Per.TiedRestrict.restrict_crys_deRham <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTerm
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def rsTerm {a b : ℕ} (σ : CG E a) (σ' : CG E b) (x : ℝ) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℂ :=
  ((sat σ w).map fun α => (α : ℂ) ^ (r + 1)).sum * ((sat σ' w).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (r + 1)).sum *
    (Ideal.absNorm w.asIdeal : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1)

def logRS (T : Finset (HeightOneSpectrum (𝓞 E))) {a b : ℕ} (σ : CG E a) (σ' : CG E b) (x : ℝ) : ℂ :=
  ∑' p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ, rsTerm σ σ' x p.1.1 p.2

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSettingGroupActionCompatStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_setting_group_action_compat : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), ∀ v : κ → OW l O, homW t ϖ H v = 0 → ∃ w, homW t ϖ F w = v := by
  first | exact @GlobalTheory.BKReal.SESExact.homW_exact_middle | exact GlobalTheory.BKReal.SESExact.homW_exact_middle | (intros; apply GlobalTheory.BKReal.SESExact.homW_exact_middle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorBcrisFrobeniusValueEqSumCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.XiDecomp

theorem toBcris_xiExt_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (w : Vec K a ι) (hwS : ∀ τ j, w τ j ∈ invL l (S O K e)) (hw : P.xiExt w ∈ P.MMl) (hd : ∀ j, P.xi (fun _ => Pi.single j 1) ∈ P.MMl), toBcris t ϖ P ⟨P.xiExt w, hw⟩ = ∑ j, ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) • toBcris t ϖ P ⟨P.xi (fun _ => Pi.single j 1), hd j⟩ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P w hwS hw hd
  have hsum : (⟨P.xiExt w, hw⟩ : P.MMl) = ∑ j, (⟨(fun τ => w τ j) • P.xi (fun _ => Pi.single j 1),
      P.smul_tot_mem_ext (fun τ => hwS τ j) (hd j)⟩ : P.MMl) := by
    apply Subtype.ext
    show P.xiExt w = _
    rw [Submodule.coe_sum]
    conv_lhs => rw [eq_sum_bas w, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show _ = (fun τ => w τ j) • P.xi (fun _ => Pi.single j 1)
    rw [PhiMod.xiExt_smul_tot, PhiMod.xi_apply, cst_single]
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext1 k
  rw [Pi.smul_apply, toBcris_apply, toBcris_apply, smul_eq_mul, ← map_mul]
  congr 1
  funext τ
  apply Subtype.ext
  simp [coordL, Matrix.mulVec_smul]

end GlobalTheory.XiDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorOneInjectiveStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_tmul_injective_locLat : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O), Function.Injective fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x := by
  first | exact @GlobalTheory.TensorOneInj.tensor_one_injective | exact GlobalTheory.TensorOneInj.tensor_one_injective | (intros; apply GlobalTheory.TensorOneInj.tensor_one_injective <;> assumption)
end

