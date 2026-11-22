import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0805
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0807
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtRead

variable {D : D7}

def IdFrame {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) : Prop :=
  ∃ hn : V.rank = n, ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
    (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn b))

variable {S T : HSp D} {n : ℕ}

def RatMatch (φ : GAf D.host.E n ≃* Bridge.Gf S) : Prop :=
  (∀ γ : ReciprocityTheory.Aut.GQ D.host.E n, ∃ γ', Bridge.ratF S γ' = φ γ) ∧
    ∀ γ', ∃ γ : ReciprocityTheory.Aut.GQ D.host.E n, Bridge.ratF S γ' = φ γ

def WtMap (B : Base S T) (φ : GAf D.host.E n ≃* Bridge.Gf S) (R : Type) [CommRing R] [IsDomain R] (e : FractionRing R →+* ℂ)
    {W : Type} [AddCommGroup W] [Module (FractionRing R) W] (ρ : Representation (FractionRing R) (ReciprocityTheory.Aut.GQ D.host.E n) W)
    (ω : W →ₛₗ[e] PolF D T.rank S.rank) : Prop :=
  Function.Injective ω ∧ (∀ w, ω w ∈ B.valSpace) ∧
    (∀ (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ' : Formalism.L2.Theta.GQ S), Bridge.ratF S γ' = φ γ →
      ∀ w, ω (ρ γ w) = B.act (γ' : GA D S) (ω w)) ∧
    (∀ h, ∀ x ∈ B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range h, x ∈ Set.range ω) ∧
    ∀ h w, ∃ c : R, c ≠ 0 ∧
      ω (algebraMap R (FractionRing R) c • w) ∈ B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range h

def LevMatch (B : Base S T) (t : Twist D Circle) (φ : GAf D.host.E n ≃* Bridge.Gf S) {K : Type} [Field K] (e : K →+* ℂ)
    (J : Subgroup (GAf D.host.E n)) (χ : J →* Kˣ) : Prop :=
  (∀ g, g ∈ J ↔ φ g ∈ B.levJ t) ∧
    ∀ g (h : g ∈ J) (h' : φ g ∈ B.levJ t), e ((χ ⟨g, h⟩ : Kˣ) : K) = ((B.levLam t ⟨φ g, h'⟩ : ℂˣ) : ℂ)

theorem finite_kP (P : Pl D.host.E) : Finite (kP P) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot

theorem isOfFinOrder_levFn {m : ℕ} (β : GL (Fin m) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ m) (x : GL (Fin m) (Lev.EAf D)) :
    IsOfFinOrder (levFn β L x) := by
  haveI : ∀ P : Pl D.host.E, Finite (kP P) := finite_kP
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℂˣ), (∀ i ∈ s, IsOfFinOrder (f i)) → IsOfFinOrder (∏ i ∈ s, f i) :=
    fun s f h => Finset.prod_induction f IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) IsOfFinOrder.one h
  unfold levFn
  refine (IsOfFinOrder.mul ?_ (hprod _ _ fun P _ => hprod _ _ fun c _ => ?_)).mul (hprod _ _ fun P _ => ?_)
  · unfold ext1
    split_ifs with h
    · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    · exact IsOfFinOrder.one
  · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)

theorem mem_range_of_finOrder {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (e : FractionRing R →+* ℂ)
    {x : FractionRing R} {z : ℂˣ} (hz : IsOfFinOrder z) (h : e x = z) : (z : ℂ) ∈ (e.comp (algebraMap R (FractionRing R))).range := by
  obtain ⟨m, hm, h1⟩ := hz.exists_pow_eq_one
  have h2 : x ^ m = 1 := e.injective (by rw [map_pow, h, ← Units.val_pow_eq_pow_val, h1, map_one, Units.val_one])
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (R := R) hm (h2 ▸ isIntegral_one))
  exact ⟨y, by rw [RingHom.comp_apply, hy, h]⟩

theorem read_abstract {G G' Γ' R W P I V : Type} [Group G] [Group G'] [Group Γ'] [CommRing R] [IsDomain R] [AddCommGroup W]
    [Module (FractionRing R) W] [AddCommGroup P] [Module ℂ P] [Finite I] [AddCommGroup V] [Module (FractionRing R) V]
    (φ : G ≃* G') (Γ J : Subgroup G) (J' : Subgroup G') (ι : Γ' → G') (e : FractionRing R →+* ℂ) (ρ : Γ → W → W) (χ : J → FractionRing R)
    (act : Γ' → P → P) (lam : J' → ℂ) (ω : W →ₛₗ[e] P) (val : Set P)
    (L : G' → Submodule (e.comp (algebraMap R (FractionRing R))).range P)
    (A : Submodule (FractionRing R) (G → W))
    (hA : ∀ f, f ∈ A ↔ (∀ (γ : Γ) g, f (γ * g) = ρ γ (f g)) ∧ ∀ (κ : J) g, f (g * κ) = χ κ • f g)
    (M : Set (G' → P))
    (hM : ∀ F, F ∈ M ↔ ((∀ h, F h ∈ val) ∧ ∀ γ h (k : J'), F (ι γ * h * k) = lam k • act γ (F h)) ∧ ∀ h, F h ∈ L h)
    (h1 : ∃ γ, ι γ = 1 ∧ ∀ x, act γ x = x) (hl1 : lam 1 = 1)
    (hr1 : ∀ γ : Γ, ∃ γ', ι γ' = φ γ) (hr2 : ∀ γ', ∃ γ : Γ, ι γ' = φ γ)
    (hinj : Function.Injective ω) (hval : ∀ w, ω w ∈ val) (heq : ∀ (γ : Γ) γ', ι γ' = φ γ → ∀ w, ω (ρ γ w) = act γ' (ω w))
    (hrange : ∀ h, ∀ x ∈ L h, x ∈ Set.range ω) (hden : ∀ h w, ∃ c : R, c ≠ 0 ∧ ω (algebraMap R (FractionRing R) c • w) ∈ L h)
    (hJ1 : ∀ g, g ∈ J ↔ φ g ∈ J') (hJ2 : ∀ g (h : g ∈ J) (h' : φ g ∈ J'), e (χ ⟨g, h⟩) = lam ⟨φ g, h'⟩)
    (hlam : ∀ k, lam k ∈ (e.comp (algebraMap R (FractionRing R))).range)
    (hact : ∀ γ h (k : J'), ∀ x ∈ L h, act γ x ∈ L (ι γ * h * k))
    (y : I → G') (hy : ∀ h, ∃ i γ, ∃ k : J', h = ι γ * y i * k) (real : V ≃ₗ[FractionRing R] A) :
    ∃ r : V →ₛₗ[e] (G' → P), Function.Injective r ∧ (∀ F ∈ M, F ∈ Set.range r) ∧
      Submodule.span (FractionRing R) {f | r f ∈ M} = ⊤ ∧ ∀ f g, r f (φ g) = ω ((real f).1 g) := by
  let r : V →ₛₗ[e] (G' → P) :=
    { toFun := fun f h => ω ((real f).1 (φ.symm h))
      map_add' := fun f f' => by funext h; simp
      map_smul' := fun c f => by funext h; simp [map_smulₛₗ] }
  have hr_apply : ∀ f g, r f (φ g) = ω ((real f).1 g) := fun f g => by
    change ω ((real f).1 (φ.symm (φ g))) = _
    rw [φ.symm_apply_apply]
  have hlaw : ∀ f γ h (k : J'), r f (ι γ * h * k) = lam k • act γ (r f h) := fun f γ' h k => by
    obtain ⟨γ, hγ⟩ := hr2 γ'
    obtain ⟨g, rfl⟩ := φ.surjective h
    obtain ⟨k, hk⟩ := k
    obtain ⟨κ, rfl⟩ := φ.surjective k
    have hκ := (hJ1 κ).2 hk
    change r f (ι γ' * φ g * φ κ) = _
    have h2 := (hA _).1 (real f).2
    rw [hγ, ← map_mul, ← map_mul, hr_apply, hr_apply, h2.2 ⟨κ, hκ⟩, h2.1, map_smulₛₗ, heq γ γ' hγ, hJ2 κ hκ hk]
  refine ⟨r, fun f f' h => ?_, fun F hF => ?_, ?_, hr_apply⟩
  · refine real.injective (Subtype.ext (funext fun g => hinj ?_))
    rw [← hr_apply, ← hr_apply, h]
  · obtain ⟨⟨-, hF3⟩, hF2⟩ := (hM F).1 hF
    choose u hu using fun g => hrange (φ g) _ (hF2 (φ g))
    have hmem : u ∈ A := by
      refine (hA u).2 ⟨fun γ g => hinj ?_, fun κ g => hinj ?_⟩
      · obtain ⟨γ', hγ⟩ := hr1 γ
        have := hF3 γ' (φ g) 1
        rw [heq γ γ' hγ, hu, hu, map_mul, ← hγ]
        simpa [hl1] using this
      · have hk := (hJ1 κ).1 κ.2
        obtain ⟨γ, hγ, hγ'⟩ := h1
        have := hF3 γ (φ g) ⟨φ κ, hk⟩
        rw [map_smulₛₗ, hu, hu, map_mul, hJ2 κ κ.2 hk]
        simpa [hγ, hγ'] using this
    refine ⟨real.symm ⟨u, hmem⟩, funext fun h => ?_⟩
    obtain ⟨g, rfl⟩ := φ.surjective h
    rw [hr_apply, real.apply_symm_apply, hu]
  · refine eq_top_iff.2 fun f _ => ?_
    haveI := Fintype.ofFinite I
    classical
    choose c hc0 hcm using fun i => hden (y i) ((real f).1 (φ.symm (y i)))
    have hd : algebraMap R (FractionRing R) (∏ i, c i) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact Finset.prod_ne_zero_iff.2 fun i _ => hc0 i
    have hm : r (algebraMap R (FractionRing R) (∏ i, c i) • f) ∈ M := by
      refine (hM _).2 ⟨⟨fun h => hval _, hlaw _⟩, fun h => ?_⟩
      obtain ⟨i, γ, k, rfl⟩ := hy h
      have e1 : r (algebraMap R (FractionRing R) (∏ i, c i) • f) (y i) =
          e (algebraMap R (FractionRing R) (∏ j ∈ Finset.univ.erase i, c j)) •
            ω (algebraMap R (FractionRing R) (c i) • (real f).1 (φ.symm (y i))) := by
        rw [← map_smulₛₗ, smul_smul, ← map_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
        change ω ((real (_ • f)).1 _) = _
        rw [map_smul]
        rfl
      have h2 : r (algebraMap R (FractionRing R) (∏ i, c i) • f) (y i) ∈ L (y i) := by
        rw [e1]
        exact Submodule.smul_mem _ (⟨_, _, rfl⟩ : (e.comp (algebraMap R (FractionRing R))).range) (hcm i)
      rw [hlaw]
      exact Submodule.smul_mem _ (⟨_, hlam k⟩ : (e.comp (algebraMap R (FractionRing R))).range) (hact γ _ k _ h2)
    have := Submodule.smul_mem _ (algebraMap R (FractionRing R) (∏ i, c i))⁻¹ (Submodule.subset_span (R := FractionRing R)
      (s := {f | r f ∈ M}) hm)
    rwa [inv_smul_smul₀ hd] at this

theorem read_cell (B : Base S T) (hB : B.Good) (t : Twist D Circle) (φ : GAf D.host.E n ≃* Bridge.Gf S) (R : Type) [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] (e : FractionRing R →+* ℂ)
    (hc : IsCoefRing (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range)
    {W : Type} [AddCommGroup W] [Module (FractionRing R) W] (ρ : Representation (FractionRing R) (ReciprocityTheory.Aut.GQ D.host.E n) W)
    (J : Subgroup (GAf D.host.E n)) (χ : J →* (FractionRing R)ˣ) (ω : W →ₛₗ[e] PolF D T.rank S.rank)
    (hr : RatMatch φ) (hω : WtMap B φ R e ρ ω) (hJ : LevMatch B t φ e J χ) {I : Type} [Finite I] (y : I → Bridge.Gf S)
    (hy : Bridge.IsReps (Bridge.ratF S) (B.levJ t) y) {V : Type} [AddCommGroup V] [Module (FractionRing R) V]
    (real : V ≃ₗ[FractionRing R] NX.TypeSpF D.host.E n (FractionRing R) ρ J χ) :
    ∃ r : V →ₛₗ[e] (Bridge.Gf S → PolF D T.rank S.rank), Function.Injective r ∧
      (∀ F ∈ B.mtLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range t, F ∈ Set.range r) ∧
      Submodule.span (FractionRing R)
        {f | r f ∈ B.mtLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range t} = ⊤ ∧
      ∀ f g, r f (φ g) = ω ((real f).1 g) := by
  refine read_abstract φ (ReciprocityTheory.Aut.GQ D.host.E n) J (B.levJ t) (Bridge.ratF S) e (fun γ => ρ γ) (fun κ => (χ κ : FractionRing R))
    (fun γ => B.act (γ : GA D S)) (fun k => ((B.levLam t k : ℂˣ) : ℂ)) ω B.valSpace
    (B.coefLat (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range) _ (fun _ => Iff.rfl) _
    (fun F => (B.mem_mtLat _ _ _).trans (and_congr_left' B.mem_formsC)) ⟨1, MonoidHom.map_one _, fun x => ?_⟩ ?_ hr.1 hr.2
    hω.1 hω.2.1 hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2 hJ.1 hJ.2 (fun k => ?_)
    (fun γ h k x hx => Base.act_mem_coefLat hB.frame hc γ h k (Base.mem_St_of_mem_levJ k.2) hx) y
    (fun h => (hy h).exists.imp fun _ h => h) real
  · change B.act 1 x = x
    rw [MonoidHom.map_one]
    rfl
  · change ((B.levLam t 1 : ℂˣ) : ℂ) = 1
    rw [MonoidHom.map_one]
    rfl
  · obtain ⟨k, hk⟩ := k
    obtain ⟨κ, rfl⟩ := φ.surjective k
    exact mem_range_of_finOrder e (isOfFinOrder_levFn _ _ _) (hJ.2 κ ((hJ.1 κ).2 hk) hk)

theorem admissible_twist_of_twisting_character {i : D.ntw.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    (h : TwOK i k Q ψ) : NX.AdmTw D i k Q ψ := by
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := h
  have hS : ∀ P ∈ Q, P ∉ D.ntw.S0 i := fun P hP => Finset.disjoint_left.1 hdisj hP
  have hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1 := Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)
  refine ⟨fun P hP => ⟨hsplit P hP, fun h => hS P hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)⟩,
    fun P hP => ⟨fun h => hS P hP (D.ntw.primes_subset_exceptional i h), fun k' h => hS P hP (D.ntw.placesOver_subset_exceptional i k' h)⟩, hopen, hanti, fun σ => ⟨k, ?_⟩,
    fun P hP A hA σ hσ => ?_⟩
  · obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  · by_contra h
    exact hP ((hram P A hA).1 ⟨σ, hσ, h⟩)

theorem eq_of_infOf_eq {m : ℕ} {a b : Fin m → ℤ} (ha : Antitone a) (hb : Antitone b) (h : NG.infOf a = NG.infOf b) : a = b := by
  have key : ∀ c : Fin m → ℤ, NG.infOf c =
      (Finset.univ.val.map fun i : Fin m => c i - (i : ℕ)).map fun z : ℤ => (z : ℂ) + ((m : ℂ) - 1) / 2 := fun c => by
    rw [NG.infOf, Multiset.map_map]
    congr 1
    funext i
    simp only [Function.comp]
    push_cast
    ring
  rw [key, key] at h
  have h2 := Multiset.map_injective (fun x y hxy => by exact_mod_cast add_right_cancel hxy) h
  have sa : ∀ c : Fin m → ℤ, Antitone c → StrictAnti fun i : Fin m => c i - (i : ℕ) := fun c hc i j hij => by
    have := hc hij.le
    have h3 : (i : ℕ) < j := hij
    beta_reduce
    omega
  have hr : Set.range (fun i : Fin m => a i - (i : ℕ)) = Set.range fun i : Fin m => b i - (i : ℕ) := by
    ext z
    have := congrArg (z ∈ ·) h2
    simpa using this
  have h4 := ((sa a ha).range_inj (sa b hb)).1 hr
  funext i
  have := congrFun h4 i
  omega

end GlobalTheory.MtRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightSpanOfIndep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HwTransfer

open MvPolynomial

variable {L : Type} [Field L] {n : ℕ} {K : Type} [Field K]

open Classical in

noncomputable def evS {S : Type} [CommRing S] (c : L →+* L) (τ : L →+* K) (X Y : Matrix (Fin n) (Fin n) S) :
    (L →+* K) × Fin n × Fin n → S := fun p =>
  if p.1 = τ then X p.2.1 p.2.2
  else if p.1 = τ.comp c then Y p.2.2 p.2.1
  else if p.2.1 = p.2.2 then 1 else 0

theorem evS_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (c : L →+* L) (τ : L →+* K)
    (X Y : Matrix (Fin n) (Fin n) S) : ψ ∘ evS c τ X Y = evS c τ (X.map ψ) (Y.map ψ) := by
  funext p
  simp only [evS, Function.comp_apply, Matrix.map_apply]
  split_ifs <;> simp

noncomputable def defect {S : Type} [CommRing S] (φ : K →+* S) (c : L →+* L) (τ : L →+* K) {ι : Type} [Fintype ι]
    (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K) (lam : Fin n → ℤ)
    (X Y : Matrix (Fin n) (Fin n) S) (i : ι) : S :=
  (∏ a, X a a ^ (-lam a).toNat) * ∑ j, eval₂ φ (evS c τ X Y) (P i j) * φ (v j) -
    (∏ a, X a a ^ (lam a).toNat) * φ (v i)

theorem defect_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (φ : K →+* S) (c : L →+* L)
    (τ : L →+* K) {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K)
    (lam : Fin n → ℤ) (X Y : Matrix (Fin n) (Fin n) S) (i : ι) :
    ψ (defect φ c τ P v lam X Y i) = defect (ψ.comp φ) c τ P v lam (X.map ψ) (Y.map ψ) i := by
  simp only [defect, map_sub, map_mul, map_prod, map_pow, map_sum, hom_eval₂, Matrix.map_apply,
    RingHom.comp_apply]
  rw [← evS_map]
  rfl

theorem defect_eq_zero_iff {F : Type} [Field F] (φ : K →+* F) (c : L →+* L) (τ : L →+* K) {ι : Type}
    [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K) (lam : Fin n → ℤ)
    (X Y : Matrix (Fin n) (Fin n) F) (hX : ∀ a, X a a ≠ 0) (i : ι) :
    defect φ c τ P v lam X Y i = 0 ↔
      ∑ j, eval₂ φ (evS c τ X Y) (P i j) * φ (v j) = (∏ a, X a a ^ lam a) * φ (v i) := by
  have key : ∀ a, X a a ^ (lam a).toNat = X a a ^ (-lam a).toNat * X a a ^ lam a := by
    intro a
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hX a)]
    congr 1
    omega
  have hu : (∏ a, X a a ^ (-lam a).toNat) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (hX a)
  simp only [defect, sub_eq_zero, key, Finset.prod_mul_distrib, mul_assoc]
  exact ⟨fun h => mul_left_cancel₀ hu h, fun h => by rw [h]⟩

end GlobalTheory.HwTransfer

namespace GlobalTheory.HwTransfer

open MvPolynomial

variable {L : Type} [Field L] {n : ℕ} {K : Type} [Field K]

theorem inv_map_of_mul {A F : Type} [CommRing A] [Field F] (ψ : A →+* F) (G : Matrix (Fin n) (Fin n) A)
    (h : G⁻¹ * G = 1) : (G.map ψ)⁻¹ = G⁻¹.map ψ := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero ψ) (map_one ψ)]

theorem defect_transfer (e : K →+* ℂ) (c : L →+* L) (τ : L →+* K) {ι : Type} [Fintype ι]
    (P : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K) (v : ι → K) (lam : Fin n → ℤ)
    (hK : ∀ B : GL (Fin n) K, B.val.BlockTriangular id → ∀ i, defect (RingHom.id K) c τ P v lam B.val (B⁻¹).val i = 0)
    (B : GL (Fin n) ℂ) (hB : B.val.BlockTriangular id) (i : ι) :
    defect e c τ P v lam B.val (B⁻¹).val i = 0 := by
  haveI : CharZero K := RingHom.charZero e
  haveI : Infinite K := inferInstance
  classical
  obtain ⟨D, hD⟩ : ∃ D : MvPolynomial (Fin n × Fin n) K, D = ∏ a, X (a, a) := ⟨_, rfl⟩
  let A := Localization.Away D
  let φA : K →+* A := (algebraMap (MvPolynomial (Fin n × Fin n) K) A).comp C
  let G : Matrix (Fin n) (Fin n) A := fun a b => if b < a then 0 else algebraMap (MvPolynomial (Fin n × Fin n) K) A (X (a, b))
  have hGtri : G.BlockTriangular id := fun a b h => by
    simp only [G]
    rw [if_pos (show b < a from h)]
  have hDA : algebraMap (MvPolynomial (Fin n × Fin n) K) A D =
      ∏ a, algebraMap (MvPolynomial (Fin n × Fin n) K) A (X (a, a)) := by
    rw [← map_prod]
    exact congrArg _ hD
  have hdet : G.det = algebraMap (MvPolynomial (Fin n × Fin n) K) A D := by
    rw [Matrix.det_of_upperTriangular hGtri, hDA]
    simp [G]
  have hunit : IsUnit G.det := hdet ▸ IsLocalization.Away.algebraMap_isUnit D
  have hGinv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hunit

  have hy : defect φA c τ P v lam G G⁻¹ i = 0 := by
    obtain ⟨⟨f, s⟩, hfs⟩ := IsLocalization.surj (Submonoid.powers D) (defect φA c τ P v lam G G⁻¹ i)
    have hf : ∀ x : Fin n × Fin n → K, eval x D ≠ 0 → eval x f = 0 := by
      intro x hx
      let ψ : A →+* K := IsLocalization.Away.lift D (g := eval x) (Ne.isUnit hx)
      have hψ : ∀ r, ψ (algebraMap (MvPolynomial (Fin n × Fin n) K) A r) = eval x r := IsLocalization.Away.lift_eq D _
      set M : Matrix (Fin n) (Fin n) K := G.map ψ with hM
      have hMtri : M.BlockTriangular id := fun a b h => by
        show ψ (G a b) = 0
        rw [hGtri h, map_zero]
      have hMd : ∀ a, M a a = x (a, a) := fun a => by
        show ψ (G a a) = x (a, a)
        simp [G, hψ]
      have hMdet : M.det ≠ 0 := by
        rw [Matrix.det_of_upperTriangular hMtri, Finset.prod_congr rfl (fun a _ => hMd a)]
        simpa [hD] using hx
      let BK := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet
      have h1 := hK BK hMtri i
      have h2 : ψ (defect φA c τ P v lam G G⁻¹ i) = 0 := by
        rw [defect_map, ← inv_map_of_mul ψ G hGinv]
        have hc : ψ.comp φA = RingHom.id K := RingHom.ext fun k => by simp [φA, hψ]
        rw [hc]
        simpa [BK, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.coe_units_inv] using h1
      have h3 := congrArg ψ hfs
      rw [map_mul, h2, zero_mul, hψ] at h3
      exact h3.symm
    have hfD : f * D = 0 := by
      apply MvPolynomial.funext
      intro x
      rw [map_mul, map_zero]
      by_cases hx : eval x D = 0
      · rw [hx, mul_zero]
      · rw [hf x hx, zero_mul]
    have hD0 : D ≠ 0 := by
      rw [hD]
      exact Finset.prod_ne_zero_iff.2 fun a _ => X_ne_zero _
    have hf0 : f = 0 := (mul_eq_zero.1 hfD).resolve_right hD0
    rw [hf0, map_zero] at hfs
    exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units A s)).1 hfs

  have hBdiag : eval₂ e (fun p => B.val p.1 p.2) D ≠ 0 := by
    have : B.val.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit |>.ne_zero
    rw [Matrix.det_of_upperTriangular hB] at this
    simpa [hD] using this
  let ψ : A →+* ℂ := IsLocalization.Away.lift D (g := eval₂Hom e (fun p => B.val p.1 p.2)) (Ne.isUnit hBdiag)
  have hψ : ∀ r, ψ (algebraMap (MvPolynomial (Fin n × Fin n) K) A r) = eval₂ e (fun p => B.val p.1 p.2) r := IsLocalization.Away.lift_eq D _
  have hGB : G.map ψ = B.val := by
    ext a b
    by_cases h : b < a
    · show ψ (G a b) = B.val a b
      rw [hGtri h, map_zero, hB h]
    · show ψ (G a b) = B.val a b
      simp [G, h, hψ]
  have hc : ψ.comp φA = e := RingHom.ext fun k => by simp [φA, hψ]
  have := congrArg ψ hy
  rw [defect_map, ← inv_map_of_mul ψ G hGinv, hGB, hc, map_zero] at this
  simpa [Matrix.coe_units_inv] using this

end GlobalTheory.HwTransfer

namespace GlobalTheory.HwTransfer

open MvPolynomial

theorem diag_ne_zero {n : ℕ} {F : Type} [Field F] (B : GL (Fin n) F) (hB : B.val.BlockTriangular id) (a : Fin n) :
    B.val a a ≠ 0 := by
  have h : B.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  rw [Matrix.det_of_upperTriangular hB] at h
  exact Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)

end GlobalTheory.HwTransfer

open MvPolynomial GlobalTheory.HwTransfer in

theorem GlobalTheory.hwAt_of_hwAtF : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ)
    (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W]
    (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (a : NG.AlgWt L n) (ω : W →ₛₗ[e] a.W),
    (∀ (κ : Type) (v : κ → W), LinearIndependent K v → LinearIndependent ℂ fun x => ω (v x)) →
    Submodule.span ℂ (Set.range ω) = ⊤ → (∀ γ w, ω (ρ γ w) = a.ρ γ (ω w)) →
    ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ τ lam → a.HWAt (e.comp τ) lam := by
  intro L _ _ _ n K _ e c hc W _ _ ρ a ω hind hspan hint τ lam h
  classical
  obtain ⟨ι, hι, hdec, b, P, hP, v, hv0, hv⟩ := h
  have hcomp : ∀ σ σ' : L →+* K, e.comp σ = e.comp σ' ↔ σ = σ' := fun σ σ' =>
    ⟨fun h => RingHom.ext fun x => e.injective (RingHom.congr_fun h x), fun h => h ▸ rfl⟩
  have hconj : ComplexEmbedding.conjugate (e.comp τ) = e.comp (τ.comp c) := by
    ext x
    have h5 := IsCMField.complexEmbedding_complexConj L (e.comp τ) x
    rw [ComplexEmbedding.conjugate_coe_eq]
    simp only [RingHom.comp_apply, hc] at h5 ⊢
    exact h5.symm
  have hli : LinearIndependent ℂ (fun i => ω (b i)) := hind ι b b.linearIndependent
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun i => ω (b i)) := by
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    rw [← b.sum_repr w, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis ι ℂ a.W := Module.Basis.mk hli hsp
  let f : (L →+* K) × Fin n × Fin n → (L →+* ℂ) × Fin n × Fin n := fun p => (e.comp p.1, p.2)
  have hev : ∀ (g : (L →+* ℂ) × Fin n × Fin n → ℂ) (Q : MvPolynomial ((L →+* K) × Fin n × Fin n) K),
      eval g (rename f (map e Q)) = eval₂ e (g ∘ f) Q := fun g Q => by rw [eval_rename, eval_map]
  refine ⟨ι, hι, hdec, b', fun i j => rename f (map e (P i j)), ?_, fun i => e (v i), ?_, ?_⟩
  · intro γ γ₀ hγ
    have h1 := hP γ γ₀ hγ
    ext i j
    rw [LinearMap.toMatrix_apply, Module.Basis.mk_apply, ← hint, ← b.sum_repr (ρ γ (b j)), map_sum]
    simp only [LinearMap.map_smulₛₗ]
    have hb' : ∀ k, ω (b k) = b' k := fun k => (Module.Basis.mk_apply hli hsp k).symm
    simp only [hb', map_sum, map_smul, Module.Basis.repr_self]
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hev]
    have h2 := congrFun (congrFun h1 i) j
    rw [LinearMap.toMatrix_apply] at h2
    rw [h2]
    change e (eval₂ (RingHom.id K) _ (P i j)) = _
    rw [hom_eval₂, RingHom.comp_id]
    rfl
  · intro h0
    apply hv0
    funext i
    exact e.injective (by simpa using congrFun h0 i)
  · intro B hB
    have hK : ∀ B : GL (Fin n) K, B.val.BlockTriangular id → ∀ i,
        defect (RingHom.id K) c τ P v lam B.val (B⁻¹).val i = 0 := by
      intro B hB i
      rw [defect_eq_zero_iff _ c τ P v lam _ _ (diag_ne_zero B hB)]
      have h3 := congrFun (hv B hB) i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at h3
      have hF : NX.evPtF c τ B = evS c τ B.val (B⁻¹).val := by
        funext p
        unfold NX.evPtF evS
        split_ifs <;> rfl
      rw [hF] at h3
      simp only [RingHom.id_apply]
      exact h3
    have hC := fun i => defect_transfer e c τ P v lam hK B hB i
    have hevC : NG.evPt (e.comp τ) B ∘ f = evS c τ B.val (B⁻¹).val := by
      funext p
      simp only [NG.evPt, evS, Function.comp_apply, f, hconj, hcomp]
    funext i
    have h4 := (defect_eq_zero_iff e c τ P v lam _ _ (diag_ne_zero B hB) i).1 (hC i)
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, hev, hevC]
    exact h4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxOfPendingStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conclusion41_of_pAdicHodge : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (C : ℝ) (CT : ℕ), 40 ≤ CT → 8 * (CT : ℝ) ≤ C → (∃ P : Pend D, admDZ P ∧ EigSpan P) → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → SumRepresentations.Conclusion41 D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionG6 D → ResidualIrreducibleRankR D → GlobalTheory.TypeLeaf.SerLoc D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D → TieInePoly D → tieChi (D := D) → PairedCharacterCondition.aux₃ (D := D) C CT := by
  first | exact @GlobalTheory.ClosingLocalInputs.main | exact GlobalTheory.ClosingLocalInputs.main | (intros; apply GlobalTheory.ClosingLocalInputs.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCpStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ramification_overPlace_of_cdvrReadingInCp : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∃ e : ℕ, OverLa (placeAt φ) T.V io e := by
  first | exact @GlobalTheory.ReadingOver.overLa_placeAt | exact GlobalTheory.ReadingOver.overLa_placeAt | (intros; apply GlobalTheory.ReadingOver.overLa_placeAt <;> assumption)
end

