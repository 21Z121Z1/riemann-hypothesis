import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCocyclesLeCoboundariesAddSelmer
section
noncomputable section

namespace GlobalTheory.Cut.SelClass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem length_le_cob_add {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R Γ M)
    (C : Submodule R (Γ → M)) (hC : C ≤ ReciprocityTheory.Gal.Z1 rho) (S : Submodule R (ReciprocityTheory.Gal.H1 rho))
    (hS : ∀ f (hf : f ∈ C), (Submodule.Quotient.mk ⟨f, hC hf⟩ : ReciprocityTheory.Gal.H1 rho) ∈ S) :
    Module.length R ↥C ≤ Module.length R ↥(C ⊓ ReciprocityTheory.Gal.B1 rho) + Module.length R ↥S := by

  let ψ : ↥C →ₗ[R] ReciprocityTheory.Gal.H1 rho :=
    ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype).mkQ ∘ₗ Submodule.inclusion hC
  have hker : ∀ x : ↥C, ψ x = 0 → (x : Γ → M) ∈ ReciprocityTheory.Gal.B1 rho := by
    intro x hx
    have h := (Submodule.Quotient.mk_eq_zero _).1 hx
    simpa using h
  have hrange : LinearMap.range ψ ≤ S := by
    rintro _ ⟨x, rfl⟩
    exact hS x.1 x.2
  let K := LinearMap.ker ψ.rangeRestrict
  have hsplit := Module.length_eq_add_of_exact K.subtype ψ.rangeRestrict
    (Submodule.subtype_injective _) ψ.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map _)

  let j : ↥K →ₗ[R] ↥(C ⊓ ReciprocityTheory.Gal.B1 rho) :=
    LinearMap.codRestrict (C ⊓ ReciprocityTheory.Gal.B1 rho) (C.subtype ∘ₗ K.subtype) (fun x => by
      refine ⟨x.1.2, hker x.1 ?_⟩
      have hx : ψ.rangeRestrict x.1 = 0 := x.2
      exact congrArg Subtype.val hx)
  have hj : Function.Injective j := by
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have hK := Module.length_le_of_injective j hj
  have hI := Module.length_le_of_injective (Submodule.inclusion hrange) (Submodule.inclusion_injective hrange)
  rw [hsplit]
  exact add_le_add hK hI

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem mk_mem_selG {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω)
    (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (P : LocPrime l)
    (nb : ∀ w, w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (A.1 w)) O)
    (Sig : Set (HeightOneSpectrum (𝓞 E))) {k : ℕ} (M : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O)
    (f : ↥(ReciprocityTheory.Gal.Z1 (WKG M)))
    (hl : ∀ w hw, (fun g => Br.phi (nb w hw) k (f.1 (Br.ι (nb w hw) g).1)) ∈
      HfD (P.PD (nb w hw).Kw) (Br.lat (nb w hw) (M.comp (Dec (F := E) (A.1 w)).subtype)))
    (hu : ∀ v, v ∉ placesOver E l → v ∉ Sig → ∀ g ∈ Ine (F := E) (A.1 v), f.1 g = 0) :
    (Submodule.Quotient.mk f : ReciprocityTheory.Gal.H1 (WKG M)) ∈ Br.selG A l P nb Sig M := by
  unfold Br.selG GaloisCohomology.SelAll GaloisCohomology.bkCond Br.LlG Sel
  refine (Submodule.mem_iInf _).2 fun v => ?_
  rw [Submodule.mem_comap]
  dsimp only
  split_ifs with h1 h2 h3
  · unfold Br.bkG
    refine Submodule.mem_map.2 ⟨_, ?_, rfl⟩
    exact hl v h2
  · exact Submodule.mem_top
  · exact Submodule.mem_top
  · have hv : v ∉ placesOver E l := h1
    unfold GaloisCohomology.unrAt H1ur
    rw [LinearMap.mem_ker]
    unfold ReciprocityTheory.Gal.resH1
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

    convert (ReciprocityTheory.Gal.B1 _).zero_mem using 1
    funext g
    exact hu v hv h3 _ g.2

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem main : ∀ (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) D.R.r)), C ≤ Z1 (WKG (WpO D.nd i ρ π)) → (∀ f ∈ C, IsFinL i (WpO D.nd i ρ π) f) → (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i C v = ⊥) → Module.length (D.nd.O i) ↥C ≤ lenCob i (WpO D.nd i ρ π) (C) + Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π) := by
  intro D i ρ π C hC hfin hine
  unfold lenCob
  refine length_le_cob_add _ C hC _ (fun f hf => ?_)
  unfold Br.selPi
  refine mk_mem_selG D.nd.plOm (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i) _ (WpO D.nd i ρ π) ⟨f, hC hf⟩ ?_ ?_
  · intro w hw
    exact hfin f hf w hw
  · intro v hv hSig g hg
    have hSv : v ∉ D.nd.S i := fun h => hSig (Or.inl h)
    have hQv : v ∉ D.nd.Q i := fun h => hSig (Or.inr h)

    have hmem : LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) D.R.r) Subtype.val f ∈ resIne i C v :=
      Submodule.mem_map_of_mem hf
    rw [hine v hv hSv hQv, Submodule.mem_bot] at hmem
    exact congrFun hmem ⟨g, hg⟩

end GlobalTheory.Cut.SelClass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthGlobalCocyclesLeSumPlacesOver
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.CountL

theorem length_le_of_semilinear {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] {σ : R →+* S} (hσ : Function.Surjective σ) (f : M →ₛₗ[σ] N)
    (hf : Function.Injective f) : Module.length R M ≤ Module.length S N := by
  have : RingHomSurjective σ := ⟨hσ⟩
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_strictMono (Submodule.map f) (Submodule.map_strictMono_of_injective hf)

theorem length_le_inf_comap_add {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] {σ : R →+* S} (hσ : Function.Surjective σ) (f : M →ₛₗ[σ] N)
    (C : Submodule R M) (A H : Submodule S N) (hC : ∀ x ∈ C, f x ∈ A) :
    Module.length R ↥C ≤
      Module.length R ↥(C ⊓ H.comap f) + Module.length S (↥A ⧸ H.comap A.subtype) := by
  let g : ↥C →ₛₗ[σ] (↥A ⧸ H.comap A.subtype) :=
    (H.comap A.subtype).mkQ.comp ((f.domRestrict C).codRestrict A fun x => hC x x.2)
  have hg : ∀ x : ↥C, x ∈ LinearMap.ker g → f x ∈ H := fun x hx =>
    (Submodule.Quotient.mk_eq_zero (H.comap A.subtype)).1 hx
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype (LinearMap.ker g).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)]
  refine add_le_add ?_ ?_
  · refine Module.length_le_of_injective
      ((C.subtype.comp (LinearMap.ker g).subtype).codRestrict (C ⊓ H.comap f)
        fun x => ⟨x.1.2, hg x.1 x.2⟩) ?_
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  · refine length_le_of_semilinear hσ ((LinearMap.ker g).liftQ g le_rfl) ?_
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

theorem exists_le_forall_le {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (K : ι → Submodule R M) (C : Submodule R M) (b : ℕ∞)
    (h : ∀ q, ∀ C₀ ≤ C, Module.length R ↥C₀ ≤ Module.length R ↥(C₀ ⊓ K q) + b) (Q : Finset ι) :
    ∃ C' : Submodule R M, C' ≤ C ∧ (∀ q ∈ Q, C' ≤ K q) ∧
      Module.length R ↥C ≤ (Q.card : ℕ∞) * b + Module.length R ↥C' := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨C₀, h₁, h₂, h₃⟩ := ih
    refine ⟨C₀ ⊓ K a, inf_le_left.trans h₁, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact inf_le_right
      · exact inf_le_left.trans (h₂ q hq)
    · rw [Finset.card_insert_of_notMem ha]
      refine h₃.trans ((add_le_add le_rfl (h a C₀ h₁)).trans (le_of_eq ?_))
      push_cast
      ring

theorem length_quot_natCast_le {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (p : ℕ) :
    Module.length S (S ⧸ Ideal.span {(p : S)}) ≤ Module.length R (R ⧸ Ideal.span {(p : R)}) := by
  refine length_le_of_semilinear (σ := e.symm.toRingHom) e.symm.surjective
    (Submodule.mapQ (Ideal.span {(p : S)}) (Ideal.span {(p : R)}) e.symm.toRingHom.toSemilinearMap ?_) ?_
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact Ideal.mem_span_singleton'.2 ⟨e.symm y, by
      show _ = e.symm (y * p)
      simp⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : e.symm x ∈ Ideal.span {(p : R)} := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx'
    refine (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton'.2 ⟨e y, ?_⟩)
    simpa using congrArg e hy

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

noncomputable def locFunS {D : D7} (i : D.nd.Loc) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    (GE D.nd → KOG (D.nd.O i) k) →ₛₗ[(D.nbr i w hw).eO.toRingHom]
      (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) where
  toFun := locFun i M w hw
  map_add' a b := by
    funext g
    exact (Br.phi (D.nbr i w hw) k).map_add _ _
  map_smul' c a := by
    funext g
    exact (Br.phi (D.nbr i w hw) k).map_smulₛₗ c _

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (e : ℕ), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocBound i w hw r Xs M e ∧ ∀ f ∈ C, InCut i r Xs M w hw f) → ∃ C' : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k), C' ≤ C ∧ (∀ f ∈ C', IsFinL i M f) ∧ Module.length (D.nd.O i) ↥C ≤ (((placesOver D.host.E (D.nd.l i)).ncard * e : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) + Module.length (D.nd.O i) ↥C' := by
  intro D i r Xs k M C e h
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin := finite_placesOver D.host.E (D.nd.l i) hl.ne_zero
  letI : Fintype ↥(placesOver D.host.E (D.nd.l i)) := hfin.fintype
  obtain ⟨C', h₁, h₂, h₃⟩ := exists_le_forall_le
    (fun q : ↥(placesOver D.host.E (D.nd.l i)) =>
      (HfD (Br.PD D.loc D.nbr i q.1 q.2) (Br.locLat D.nbr i q.1 q.2 M)).comap (locFunS i M q.1 q.2))
    C ((e : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i)) (by
      rintro ⟨w, hw⟩ C₀ hC₀
      refine (length_le_inf_comap_add (D.nbr i w hw).eO.surjective (locFunS i M w hw) C₀
        (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Xs M)) _
        (fun f hf => (h w hw).2 f (hC₀ hf))).trans (add_le_add le_rfl ?_)
      refine le_trans (h w hw).1 (mul_le_mul' le_rfl ?_)
      unfold lenOl lenQ
      rw [Br.PD_p]
      exact length_quot_natCast_le (D.nbr i w hw).eO _) Finset.univ
  refine ⟨C', h₁, fun f hf w hw => h₂ ⟨w, hw⟩ (Finset.mem_univ _) hf, ?_⟩
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← mul_assoc] at h₃
  rw [Nat.cast_mul]
  exact h₃

end GlobalTheory.Cut.CountL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisedGlobalCocyclesInLocalSpan
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.LocCoc

theorem factor {O K Γ X W : Type} [CommRing O] [IsNoetherianRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) [Group Γ] [Fintype X] [AddCommGroup W] [Module O W] {n : ℕ}
    (P : X → Prop) (A : X → (Γ →* Matrix (Fin n) (Fin n) O)) (E : X → Matrix (Fin n) (Fin n) O)
    (y : Γ → X → Matrix (Fin n) (Fin n) O) (hy : ∀ γ x, y γ x = (A x γ - 1) * E x)
    (φ : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] W) (ρ : Γ → W →ₗ[O] W)
    (h1 : ∀ γ δ, φ ((fun x => A x γ) * y δ) = ρ γ (φ (y δ)))
    (h0 : ∀ z ∈ Submodule.span O (Set.range y), (∀ x, P x → z x = 0) → φ z = 0) :
    ∃ (a : ℕ) (q : Fin a → X) (_ : ∀ j, P (q j)) (E' : Fin a → Fin n → K)
      (Y : Submodule O (Fin a → Fin n → K)) (_ : Y.FG)
      (hst : ∀ γ : Γ, ∀ z ∈ Y, (fun j => (mapM (algebraMap O K) (A (q j)) γ).mulVec (z j)) ∈ Y)
      (hE : ∀ γ : Γ, (fun j => (mapM (algebraMap O K) (A (q j)) γ).mulVec (E' j) - E' j) ∈ Y)
      (φ' : ↥Y →ₗ[O] W),
      (∀ (γ : Γ) (z : ↥Y), φ' ⟨_, hst γ z.1 z.2⟩ = ρ γ (φ' z)) ∧ ∀ γ, φ' ⟨_, hE γ⟩ = φ (y γ) := by
  classical
  let e := (Fintype.equivFin ({x // P x} × Fin n)).symm
  let L : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] (Fin (Fintype.card ({x // P x} × Fin n)) → Fin n → K) :=
    { toFun := fun z j s => algebraMap O K (z (e j).1.1 s (e j).2)
      map_add' := fun a b => by funext j s; simp
      map_smul' := fun c a => by funext j s; simp [Algebra.smul_def] }
  have key : ∀ (γ : Γ) (z : X → Matrix (Fin n) (Fin n) O),
      (fun j => (mapM (algebraMap O K) (A (e j).1.1) γ).mulVec (L z j)) = L ((fun x => A x γ) * z) := by
    intro γ z
    funext j s
    show ∑ t, algebraMap O K (A (e j).1.1 γ s t) * algebraMap O K (z (e j).1.1 t (e j).2) =
      algebraMap O K (∑ t, A (e j).1.1 γ s t * z (e j).1.1 t (e j).2)
    simp
  let Y0 := Submodule.span O (Set.range y)
  have hmul : ∀ γ δ, (fun x => A x γ) * y δ = y (γ * δ) - y γ := by
    intro γ δ
    funext x
    simp only [Pi.mul_apply, Pi.sub_apply, hy, map_mul]
    noncomm_ring
  have hst0 : ∀ γ, ∀ z ∈ Y0, (fun x => A x γ) * z ∈ Y0 ∧ φ ((fun x => A x γ) * z) = ρ γ (φ z) := by
    intro γ z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨δ, rfl⟩ := hz
      refine ⟨?_, h1 γ δ⟩
      rw [hmul]
      exact Y0.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb =>
      rw [mul_add, map_add, map_add, map_add, ha.2, hb.2]
      exact ⟨Y0.add_mem ha.1 hb.1, rfl⟩
    | smul c a _ ha =>
      rw [mul_smul_comm, map_smul, map_smul, map_smul, ha.2]
      exact ⟨Y0.smul_mem c ha.1, rfl⟩
  have hLE : ∀ γ, (fun j => (mapM (algebraMap O K) (A (e j).1.1) γ).mulVec (L E j) - L E j) = L (y γ) := by
    intro γ
    have : y γ = (fun x => A x γ) * E - E := by
      funext x
      simp [hy, sub_mul]
    rw [this, map_sub, ← key]
    rfl
  let L0 := L.domRestrict Y0
  have hker : LinearMap.ker L0 ≤ LinearMap.ker (φ.domRestrict Y0) := by
    intro z hz
    refine h0 z.1 z.2 fun x hx => ?_
    ext s t
    apply hinj
    have := congrFun (congrFun (LinearMap.mem_ker.mp hz) (e.symm (⟨x, hx⟩, t))) s
    simpa [L0, L] using this
  let φ' : ↥(LinearMap.range L0) →ₗ[O] W :=
    ((LinearMap.ker L0).liftQ (φ.domRestrict Y0) hker) ∘ₗ (L0.quotKerEquivRange.symm : _ →ₗ[O] _)
  have hφ' : ∀ (z : Y0) (h : L z.1 ∈ LinearMap.range L0), φ' ⟨L z.1, h⟩ = φ z.1 := by
    intro z h
    have : L0.quotKerEquivRange.symm ⟨L z.1, h⟩ = (LinearMap.ker L0).mkQ z :=
      L0.quotKerEquivRange_symm_apply_image z h
    simp only [φ', LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  refine ⟨_, fun j => (e j).1.1, fun j => (e j).1.2, L E, LinearMap.range L0, ?_, ?_, ?_, φ', ?_, ?_⟩
  · rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  · rintro γ _ ⟨z, rfl⟩
    exact ⟨⟨_, (hst0 γ z.1 z.2).1⟩, (key γ z.1).symm⟩
  · intro γ
    exact ⟨⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩, (hLE γ).symm⟩
  · rintro γ ⟨_, z, rfl⟩
    have h2 := hφ' ⟨_, (hst0 γ z.1 z.2).1⟩ ⟨⟨_, (hst0 γ z.1 z.2).1⟩, rfl⟩
    have h3 := hφ' z ⟨z, rfl⟩
    refine Eq.trans (Eq.trans (congrArg φ' (Subtype.ext ?_)) h2) ?_
    · exact key γ z.1
    rw [(hst0 γ z.1 z.2).2, ← h3]
    rfl
  · intro γ
    have h2 := hφ' ⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩ ⟨⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩, rfl⟩
    exact Eq.trans (congrArg φ' (Subtype.ext (hLE γ))) h2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i)

theorem inR'_tw (γ : GE D.nd) : InR' D.nd r S fun x' => rTwO D.nd i r (S.p x') γ := by
  refine ⟨1, fun _ => algebraMap (D.nd.O i) _ (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i), fun _ => γ,
    fun _ => S.T'.algebraMap_mem _, ?_⟩
  funext x'
  simp [rTwO, twistM]

theorem inR'_one : InR' D.nd r S 1 := by
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, ?_⟩
  funext x'
  simp

theorem inY_yg (γ : GE D.nd) : InY D.nd r S (yg D.nd r S γ) :=
  ⟨1, fun _ => 1, fun _ => γ, fun _ => inR'_one i r S, by simp⟩

theorem inY_of_span (z : S.X' → MatN D.nd i)
    (hz : z ∈ Submodule.span (D.nd.O i) (Set.range (yg D.nd r S))) : InY D.nd r S z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨δ, rfl⟩ := hz
    exact inY_yg i r S δ
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, a, γ, ha, rfl⟩ := ha
    obtain ⟨m', a', γ', ha', rfl⟩ := hb
    refine ⟨m + m', Fin.append a a', Fin.append γ γ', fun k => ?_, ?_⟩
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simpa using ha k
      · simpa using ha' k
    · rw [Fin.sum_univ_add]
      simp
  | smul c a _ ha =>
    obtain ⟨m, a, γ, ha, rfl⟩ := ha
    refine ⟨m, fun k => c • a k, γ, fun k => ?_, ?_⟩
    · obtain ⟨m', f, g, hf, h⟩ := ha k
      refine ⟨m', fun j => c • f j, g, fun j => S.T'.smul_mem (hf j) c, ?_⟩
      funext x'
      simp [h, Finset.smul_sum, mul_smul]
    · simp [Finset.smul_sum]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem inCut_of_cocW (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i))
    (hψ : ∀ γ, ψ (fun x' => rTwO D.nd i r (S.p x') γ) = M γ)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (f : GE D.nd → KOG (D.nd.O i) k) (hf : f ∈ cocW i r S Xs ψ) : InCut i r Xs M w hw f := by
  unfold cocW at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, h1, h0, rfl⟩ := hf
    obtain ⟨a, q, hq, E', Y, hY, hst, hE, φ', h2, h3⟩ :=
      factor (K := KK D.nd i) (IsFractionRing.injective _ _) (fun x' => S.p x' ∈ Xs)
        (fun x' => rTwO D.nd i r (S.p x')) (Eel D.nd S) (yg D.nd r S)
        (fun γ x' => by simp [yg, rTwO, twistM, sub_mul]) φ (fun γ => WKG M γ)
        (fun γ δ => by
          rw [h1 _ (inR'_tw i r S γ) _ (inY_yg i r S δ), hψ]
          obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (φ (yg D.nd r S δ))
          rw [← hu]
          rfl)
        (fun z hz => h0 z (inY_of_span i r S z hz))
    apply Submodule.subset_span
    refine ⟨a, fun j => S.p (q j), hq, E', Y, hY, hst, hE, φ', h2, ?_⟩
    funext g
    exact congrArg (Br.phi (D.nbr i w hw) k) (h3 _).symm
  | zero =>
    have e : locFun i M w hw 0 = 0 := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_zero
    unfold InCut
    rw [e]
    exact Submodule.zero_mem _
  | add f f' _ _ h h' =>
    have e : locFun i M w hw (f + f') = locFun i M w hw f + locFun i M w hw f' := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_add _ _
    unfold InCut at *
    rw [e]
    exact Submodule.add_mem _ h h'
  | smul c f _ h =>
    have e : locFun i M w hw (c • f) =
        ((D.nbr i w hw).eO c : Br.OLL D.nbr i w hw) • locFun i M w hw f := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_smulₛₗ c _
    unfold InCut at *
    rw [e]
    exact Submodule.smul_mem _ _ h

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ cocRho i r S Xs, InCut i r Xs (WpO D.nd i ρ π) w hw f) ∧ ∀ c : Fin D.R.t, ∀ f ∈ cocChi i r S Xs c, InCut i r Xs (chiRatO D.nd i ((c : ℕ) + 1)) w hw f := by
  intro D i r ρ π Xs S _ hG _ w hw
  obtain ⟨-, hdec, hψ, -, -, -, -, -, -, ⟨hπ, -⟩, -⟩ := hG
  have key : ∀ γ u, (((S.ψρ fun x' => rTwO D.nd i r (S.p x') γ).map (toK D.nd i)).mulVec (S.e u).1,
      fun c : Fin D.R.t => toK D.nd i (S.ψχ c fun x' => rTwO D.nd i r (S.p x') γ) * (S.e u).2 c) =
      toK D.nd i (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((mapM (toK D.nd i) (rhoO D.nd i ρ π) γ).mulVec (S.e u).1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) γ : (D.nd.O i)ˣ) : D.nd.O i) * (S.e u).2 c) := by
    intro γ u
    rw [← hψ _ (inR'_tw i r S γ) u, ← hdec, ← map_smul, hπ, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [mapM, rTwO, twistM]
  refine ⟨fun f hf => inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf,
    fun c f hf => inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf⟩
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.1 p) (key γ (S.e.symm (Pi.single q 1, 0)))
    simpa [mapM, WpO, twistM] using h
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.2 c) (key γ (S.e.symm (0, Pi.single c 1)))
    obtain rfl : p = q := Subsingleton.elim _ _
    simpa [chiRatO, twistM, mul_comm] using h

end GlobalTheory.Cut.LocCoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfIsIntegral
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
open scoped Formalism.Per

namespace GlobalTheory.ExpImage.EmbFil

theorem mem_range_of_isIntegral {F Ω L B : Type*} [Field F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]
    [CommRing L] [Algebra F L] [CommRing B] [IsDomain B] [Algebra F B] [Algebra Ω B]
    [IsScalarTower F Ω B] (ι : L →ₐ[F] B) {x : L} (hx : IsIntegral F x) :
    ∃ a : Ω, algebraMap Ω B a = ι x :=
  IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω) (K := integralClosure Ω B) |>.2
    ⟨ι x, (hx.map ι).tower_top⟩ |>.imp fun _ h => congrArg Subtype.val h

theorem algebraMap_mem_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    (T : LocTied l P AI) (a : Om l) : algebraMap (Om l) P.R.BdR a ∈ GlobalTheory.ExpImage.FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om a
  obtain ⟨-, hone, -⟩ := GlobalTheory.MemLoc.filD_laws l
  refine (T.fil _ 0 _).2 ?_
  have := Submodule.smul_mem _ y hone
  rwa [Algebra.smul_def, mul_one, ← h1] at this

theorem emb_mem_fil_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (LL : FinExt l) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥LL.1),
      ι x ∈ GlobalTheory.ExpImage.FilB P 0 := by
  intro l _ P AI T LL ι x
  have := (GlobalTheory.Per.TiedField.tied_field l P AI T).1.isDomain
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨a, ha⟩ := mem_range_of_isIntegral (Ω := Om l) ι (IsIntegral.of_finite ℚ_[l] x)
  rw [← ha]
  exact algebraMap_mem_zero T a

end GlobalTheory.ExpImage.EmbFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOfQBMemLatStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_of_qB_mem_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M n : ℕ), 1 ≤ M → ∀ z : ℚ_[l], qB P z ∈ Lat AI M n → ‖z‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  first | exact @GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat | exact GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat | (intros; apply GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1fStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_corestriction_H1f : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LiftingTheory.adm20 D HW F := by
  first | exact @GlobalTheory.res_cor_H1f | exact GlobalTheory.res_cor_H1f | (intros; apply GlobalTheory.res_cor_H1f <;> assumption)
end

