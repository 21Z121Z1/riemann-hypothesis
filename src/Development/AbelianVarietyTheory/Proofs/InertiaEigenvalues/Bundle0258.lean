import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.AdmClosure

section Lat

variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
variable {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

def between [IsDomain O] [IsPrincipalIdealRing O] (L₁ L₂ : Lattice (O := O) ρ) (N : Submodule O V)
    (h₁ : N ≤ L₁.T) (h₂ : L₂.T ≤ N) (hs : ∀ g, ∀ x ∈ N, ρ g x ∈ N) : Lattice (O := O) ρ where
  T := N
  stable := hs
  fg := L₁.fg.of_le h₁
  free := by
    haveI := L₁.free
    haveI : Module.Finite O L₁.T := Module.Finite.iff_fg.mpr L₁.fg
    haveI : Module.Finite O (N.comap L₁.T.subtype) := inferInstance
    haveI : Module.Free O (N.comap L₁.T.subtype) := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.comapSubtypeEquivOfLe h₁)
  span := by
    rw [eq_top_iff, ← L₂.span]
    exact Submodule.span_mono h₂

variable {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def prodEquiv (A : Submodule O V) (B : Submodule O V') : ↥(A.prod B) ≃ₗ[O] (↥A × ↥B) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def prodLattice (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') : Lattice (O := O) (ρ.prod ρ') where
  T := L.T.prod L'.T
  stable := fun g x hx => ⟨L.stable g _ hx.1, L'.stable g _ hx.2⟩
  fg := L.fg.prod L'.fg
  free := by
    haveI := L.free
    haveI := L'.free
    exact Module.Free.of_equiv (prodEquiv L.T L'.T).symm
  span := by
    have h := Submodule.span_prod_eq (R := LL) (s := (L.T : Set V)) (t := (L'.T : Set V')) L.T.zero_mem L'.T.zero_mem
    rw [L.span, L'.span, Submodule.prod_top] at h
    exact h

end Lat

section Bundled

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

def prodLoc (T T' : LocLat G Qp LL O) : LocLat G Qp LL O where
  V := T.V × T'.V
  ρ := T.ρ.prod T'.ρ
  cont := fun x => (T.cont x.1).prodMk (T'.cont x.2)
  L := prodLattice T.L T'.L

end Bundled

def appendEquiv {R : Type} [CommRing R] {A : Type 1} (W : A → Type) [∀ x, AddCommGroup (W x)] [∀ x, Module R (W x)]
    {ι κ : Type} (F : ι → A) (F' : κ → A) :
    ((∀ j, W (F j)) × (∀ j, W (F' j))) ≃ₗ[R] (∀ j : ι ⊕ κ, W (Sum.elim F F' j)) where
  toFun x j := match j with
    | .inl a => x.1 a
    | .inr b => x.2 b
  invFun y := (fun a => y (.inl a), fun b => y (.inr b))
  map_add' _ _ := by funext j; cases j <;> rfl
  map_smul' _ _ := by funext j; cases j <;> rfl
  left_inv _ := rfl
  right_inv _ := by funext j; cases j <;> rfl

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {t : ℕ} {Ut : ZMod n → Multiset ℤ}

theorem sumFull_prod [IsTopologicalRing LL] {μ μ' : ℕ} {T T' : LocLat G Qp LL O} (h : SumFull PD emb Γ t Ut μ T)
    (h' : SumFull PD emb Γ t Ut μ' T') : SumFull PD emb Γ t Ut (μ + μ') (prodLoc T T') := by
  obtain ⟨F, hF, e, he⟩ := h
  obtain ⟨F', hF', e', he'⟩ := h'
  let s : Fin (μ + μ') ≃ Fin μ ⊕ Fin μ' := finSumFinEquiv.symm
  have key : ∀ (g : G) (x : T.V × T'.V) (j : Fin μ ⊕ Fin μ'),
      appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F' (e (T.ρ g x.1), e' (T'.ρ g x.2)) j =
        (Sum.elim F F' j).ρ g (appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F' (e x.1, e' x.2) j) := by
    intro g x j
    cases j with
    | inl a => exact he g x.1 a
    | inr b => exact he' g x.2 b
  refine ⟨fun j => Sum.elim F F' (s j), fun j => ?_,
    ((e.prodCongr e').trans (appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F')).trans
      (LinearEquiv.piCongrLeft LL (fun j => (Sum.elim F F' j).V) s).symm, fun g x j => key g x (s j)⟩
  beta_reduce
  cases s j with
  | inl a => exact hF a
  | inr b => exact hF' b

variable {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    {π : Representation O G M} {π' : Representation O G M'}

theorem admissible_prod [IsTopologicalRing LL] (h : Admissible PD emb Γ t Ut π) (h' : Admissible PD emb Γ t Ut π') :
    Admissible PD emb Γ t Ut (π.prod π') := by
  obtain ⟨hf, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  obtain ⟨hf', μ', T', hT', L₂', p', hle', hp', hg', hk'⟩ := h'
  refine ⟨inferInstance, μ + μ', prodLoc T T', sumFull_prod hT hT', prodLattice L₂ L₂',
    (p.prodMap p') ∘ₗ (prodEquiv T.L.T T'.L.T).toLinearMap, Submodule.prod_mono hle hle',
    (hp.prodMap hp').comp (prodEquiv T.L.T T'.L.T).surjective, fun g x => ?_, fun x => ?_⟩
  · exact Prod.ext (hg g (prodEquiv T.L.T T'.L.T x).1) (hg' g (prodEquiv T.L.T T'.L.T x).2)
  · exact Prod.ext_iff.trans (and_congr (hk (prodEquiv T.L.T T'.L.T x).1) (hk' (prodEquiv T.L.T T'.L.T x).2))

variable [IsDomain O] [IsPrincipalIdealRing O]

theorem admissible_of_surjective (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (hs : Function.Surjective f) (h : Admissible PD emb Γ t Ut π) : Admissible PD emb Γ t Ut π' := by
  obtain ⟨hfin, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  let N : Submodule O T.V := (LinearMap.ker (f ∘ₗ p)).map T.L.T.subtype
  have hN : ∀ x : T.L.T, (x : T.V) ∈ N ↔ f (p x) = 0 := fun x =>
    ⟨fun ⟨_, hy, e⟩ => (Subtype.ext e : _ = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have h₁ : N ≤ T.L.T := Submodule.map_subtype_le _ _
  refine ⟨Finite.of_surjective f hs, μ, T, hT, between T.L L₂ N h₁ (fun x hx => ?_) (fun g x hx => ?_),
    f ∘ₗ p, h₁, hs.comp hp, fun g x => ?_, fun x => (hN x).symm⟩
  · refine (hN ⟨x, hle hx⟩).mpr ?_
    rw [(hk _).mpr hx, map_zero]
  · refine (hN (latRep T.L g ⟨x, h₁ hx⟩)).mpr ?_
    rw [hg, hf, (hN ⟨x, h₁ hx⟩).mp hx, map_zero]
  · simp only [LinearMap.comp_apply, hg, hf]

theorem admissible_of_injective (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (hi : Function.Injective f) (h : Admissible PD emb Γ t Ut π') : Admissible PD emb Γ t Ut π := by
  obtain ⟨hfin, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  let N : Submodule O T.V := ((LinearMap.range f).comap p).map T.L.T.subtype
  have hN : ∀ x : T.L.T, (x : T.V) ∈ N ↔ p x ∈ LinearMap.range f := fun x =>
    ⟨fun ⟨_, hy, e⟩ => (Subtype.ext e : _ = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have h₁ : N ≤ T.L.T := Submodule.map_subtype_le _ _
  have h₂ : L₂.T ≤ N := fun x hx => by
    refine (hN ⟨x, hle hx⟩).mpr ?_
    rw [(hk _).mpr hx]
    exact zero_mem _
  have hs : ∀ g, ∀ x ∈ N, T.ρ g x ∈ N := fun g x hx => by
    refine (hN (latRep T.L g ⟨x, h₁ hx⟩)).mpr ?_
    obtain ⟨y, hy⟩ := (hN ⟨x, h₁ hx⟩).mp hx
    exact ⟨π g y, by rw [hg, hf, hy]⟩
  let q : N →ₗ[O] M := (LinearEquiv.ofInjective f hi).symm.toLinearMap ∘ₗ
    (p ∘ₗ Submodule.inclusion h₁).codRestrict (LinearMap.range f) (fun x => (hN ⟨x, h₁ x.2⟩).mp x.2)
  have hq : ∀ x : N, f (q x) = p ⟨x, h₁ x.2⟩ := fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective f hi).apply_symm_apply ⟨_, (hN ⟨x, h₁ x.2⟩).mp x.2⟩)
  refine ⟨Finite.of_injective f hi, μ, withLat T (between T.L L₂ N h₁ h₂ hs), hT.withLat _, L₂, q, h₂,
    fun y => ?_, fun g x => hi ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := hp (f y)
    exact ⟨⟨x.1, (hN x).mpr ⟨y, hx.symm⟩⟩, hi ((hq _).trans hx)⟩
  · exact (hq _).trans ((hg g ⟨x.1, h₁ x.2⟩).trans ((congrArg (π' g) (hq x).symm).trans (hf g _).symm))
  · refine Iff.trans ?_ (hk ⟨x.1, h₁ x.2⟩)
    rw [← hq x, ← map_zero f]
    exact hi.eq_iff.symm

end Per

theorem admissible_closed : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Closed := by
  intro l _ P S M M' _ _ _ _ π π'
  obtain ⟨⟨hD, hDV, -⟩, -, -, hT, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  exact ⟨fun f hf => ⟨admissible_of_injective f hf, admissible_of_surjective f hf⟩, admissible_prod⟩

end GlobalTheory.AdmClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CLLUnitIntervalLe
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem cLL_unit_interval_le : ∀ (l h N v : ℕ) (U : Finset ℤ) (U' : Set ℤ), l.Prime → 1 ≤ N → U' ⊆ U → U.card ≤ N →
    (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) → v ≤ LocalSituation.mN l 1 (h + h) - 1 →
    LocalSituation.cLL l (LocalSituation.mN l 1 (h + h)) v U' 0 1 ≤ 5 + Nat.log l (2 * h) + N * (4 + 2 * Nat.log l (2 * h)) := by
  classical
  intro l h N v U U' hl hN hU hcard hb hv
  haveI : Fact l.Prime := ⟨hl⟩
  unfold LocalSituation.cLL LocalSituation.mN LocalSituation.rI LocalSituation.n0 at *
  set L := Nat.log l (2 * h) with hL
  set n0 := sInf {n | h + h ≤ l ^ n * (l - 1)} with hn0
  have hl1 : 1 < l := hl.one_lt

  have hn0le : n0 ≤ L + 1 := by
    apply Nat.sInf_le
    show h + h ≤ l ^ (L + 1) * (l - 1)
    have h1 : 2 * h < l ^ (L + 1) := Nat.lt_pow_succ_log_self hl1 (2 * h)
    have h2 : l ^ (L + 1) ≤ l ^ (L + 1) * (l - 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hI : Finset.Ico (0 : ℤ) 1 = {0} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_singleton]

  have hterm : ∀ u ∈ U,
      (∑ᶠ (_ : u ∈ U') (_ : u ≠ 0), (2 * 1 + n0 + 1 + LocalSituation.vZ l (u - 0))) ≤ 4 + 2 * L := by
    intro u hu
    have hz : LocalSituation.vZ l u ≤ Nat.log l h := vZ_le_log l h u (hb u hu)
    have hlog : Nat.log l h ≤ L := Nat.log_mono_right (by omega)
    simp only [finsum_eq_if, sub_zero]
    split_ifs <;> omega

  have hS : (∑ᶠ (u : ℤ) (_ : u ∈ U') (_ : u ≠ 0), (2 * 1 + n0 + 1 + LocalSituation.vZ l (u - 0)))
      ≤ N * (4 + 2 * L) := by
    rw [finsum_eq_sum_of_support_subset _ (s := U) ?_]
    · calc _ ≤ U.card • (4 + 2 * L) := Finset.sum_le_card_nsmul _ _ _ hterm
        _ ≤ N * (4 + 2 * L) := by
          rw [smul_eq_mul]
          exact Nat.mul_le_mul_right _ hcard
    · intro u hu
      rw [Function.mem_support] at hu
      by_contra hnot
      have hnU' : u ∉ U' := fun h' => hnot (Finset.mem_coe.mpr (hU h'))
      exact hu (by simp only [finsum_eq_if, if_neg hnU'])
  have hNL : 1 ≤ N * (4 + 2 * L) := by
    have := Nat.mul_le_mul hN (show 1 ≤ 4 + 2 * L by omega)
    omega
  have hmax := max_le hNL hS
  omega

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1H0TransportLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H1_H0_transport_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I) (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M] [DiscreteTopology M] (e : (↥LA.T ⧸ I) ≃+ M) (rho : Representation (ZMod N) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA I hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → Nat.card (QuotientCohomology LA I hI) = Nat.card (ReciprocityTheory.Gal.H1 rho) ∧ Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  first | exact @GlobalTheory.GaloisTransport.card_H1_H0_transport | exact GlobalTheory.GaloisTransport.card_H1_H0_transport | (intros; apply GlobalTheory.GaloisTransport.card_H1_H0_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LocalEulerFormula
section
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.EulerFree

theorem card_Z1_of_invariants_eq_bot {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module O M] (π : Representation O G M)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (h0 : π.invariants = ⊥) :
    Nat.card (ReciprocityTheory.Def.Z1 π ⊤) = Nat.card (ReciprocityTheory.Def.H1 π ⊤) * Nat.card M := by
  have hle : ReciprocityTheory.Def.B1 π ⊤ ≤ ReciprocityTheory.Def.Z1 π ⊤ := by
    rintro _ ⟨m, -, rfl⟩
    refine ⟨⟨(hlc m).comp (fun x => x - m), fun _ => Submodule.mem_top⟩, ?_⟩
    funext x
    change π x.1 (π x.2 m - m) - (π (x.1 * x.2) m - m) + (π x.1 m - m) = 0
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel
  have h1 := Submodule.card_eq_card_quotient_mul_card
    ((ReciprocityTheory.Def.B1 π ⊤).submoduleOf (ReciprocityTheory.Def.Z1 π ⊤))
  have h2 : Nat.card ((ReciprocityTheory.Def.B1 π ⊤).submoduleOf (ReciprocityTheory.Def.Z1 π ⊤)) =
      Nat.card (ReciprocityTheory.Def.B1 π ⊤) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hinj : Function.Injective (ReciprocityTheory.Def.d0 π) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff, ← h0]
    intro m hm g
    exact sub_eq_zero.1 (congrFun (LinearMap.mem_ker.1 hm) g)
  have h3 : Nat.card (ReciprocityTheory.Def.B1 π ⊤) = Nat.card M :=
    (Nat.card_congr (Submodule.topEquiv.symm.trans
      (Submodule.equivMapOfInjective _ hinj ⊤)).toEquiv).symm
  rw [h1, h2, h3, mul_comm]

theorem card_H1_of_euler (R O G G' : Type) [CommRing R] [CommRing O] [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R G M) (hrho : ReciprocityTheory.Gal.ContAction rho) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (π : Representation O G' M) (ha : ∀ g m, rho g m = π (φ.symm g) m)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (h0 : π.invariants = ⊥)
    (h2 : Subsingleton (ReciprocityTheory.Def.H2 π ⊤)) :
    Nat.card (ReciprocityTheory.Def.H1 π ⊤) = Nat.card M ^ d := by
  have ha' : ∀ g m, rho (φ g) m = π g m := fun g m => by rw [ha, φ.symm_apply_apply]
  have hH0 : Nat.card (ReciprocityTheory.Gal.H0 rho) = 1 := by
    have : ReciprocityTheory.Gal.H0 rho = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have : m ∈ π.invariants := fun g => by rw [← ha']; exact hm (φ g)
      rw [h0] at this
      exact this
    rw [this]
    exact Nat.card_unique
  have hH2 : Nat.card (ReciprocityTheory.Gal.H2 rho) = 1 := by
    have : Subsingleton (ReciprocityTheory.Gal.H2 rho) := by
      refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun z _ => ?_)
      let z' : ReciprocityTheory.Def.Z2 π ⊤ := ⟨fun x => z.1 (φ x.1, φ x.2),
        ⟨(IsLocallyConstant.iff_continuous _).2 (z.2.1.comp
          ((hφ.1.comp continuous_fst).prodMk (hφ.1.comp continuous_snd))), fun _ => Submodule.mem_top⟩, by
        funext x
        have := z.2.2 (φ x.1) (φ x.2.1) (φ x.2.2)
        rw [ha', ← map_mul, ← map_mul] at this
        exact this⟩
      have hz' : z' ∈ (ReciprocityTheory.Def.B2 π ⊤).submoduleOf (ReciprocityTheory.Def.Z2 π ⊤) := by
        rw [Submodule.Quotient.subsingleton_iff.1 h2]
        exact Submodule.mem_top
      obtain ⟨b, hb, hbz⟩ := hz'
      refine ⟨fun g => b (φ.symm g), hb.1.continuous.comp hφ.2, ?_⟩
      funext x
      have h : π (φ.symm x.1) (b (φ.symm x.2)) - b (φ.symm x.1 * φ.symm x.2) + b (φ.symm x.1) =
          z.1 (φ (φ.symm x.1), φ (φ.symm x.2)) := congrFun hbz (φ.symm x.1, φ.symm x.2)
      rw [φ.apply_symm_apply, φ.apply_symm_apply, ← map_mul, ← ha] at h
      exact h
    exact Nat.card_unique
  have hZ := GlobalTheory.CocycleCount.card_cocycles_mul_invariants_discrete _ _ M rho hrho
  let E : ↥(ReciprocityTheory.Def.Z1 π ⊤) ≃ ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, cocycle_mul]⟩
      invFun := fun c => ⟨fun g => c.1 (φ g),
        ⟨(IsLocallyConstant.iff_continuous _).2 (c.2.1.comp hφ.1), fun _ => Submodule.mem_top⟩, by
          funext x
          have := c.2.2 (φ x.1) (φ x.2)
          rw [ha', ← map_mul] at this
          change π x.1 (c.1 (φ x.2)) - c.1 (φ (x.1 * x.2)) + c.1 (φ x.1) = 0
          rw [this]
          abel⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.symm_apply_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.apply_symm_apply g)) }
  have hM : 0 < Nat.card M := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hM
  rw [← card_Z1_of_invariants_eq_bot π hlc h0, Nat.card_congr E]
  rw [hEu, hH0, hH2] at hZ
  simpa using hZ

theorem card_H1_eq_pow :
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Finite M] (π : Representation O ↥(GK K) M), (∀ m : M, l • m = 0) → (∀ m, IsLocallyConstant fun g => π g m) → π.invariants = ⊥ → Subsingleton (ReciprocityTheory.Def.H2 π ⊤) → Nat.card (ReciprocityTheory.Def.H1 π ⊤) = Nat.card M ^ Module.finrank ℚ_[l] ↥K.1 := by
  intro hE l _ K O M _ _ _ _ π hl hlc h0 h2
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ 1 • m = 0 := fun m => by rw [pow_one, hl]
  have _ : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule hr'
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ 1)) (Formalism.GaloisCohomology.GK l K.1) M :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => (π (φ.symm g)).toAddMonoidHom)
      (fun m => by simp) (fun g h m => by simp)
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  exact card_H1_of_euler _ O _ _ φ hφ M rho hrho _ (hE l K.1 hK 1 M rho Nat.one_pos hrho) π
    (fun _ _ => rfl) hlc h0 h2

end GlobalTheory.EulerFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryOfFiniteIndex
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.NL.FiniteRestrictionH1f

theorem coboundary_of_finiteIndex {G M k : Type} [Group G] [Field k] [CharZero k] [AddCommGroup M]
    [Module k M] (a : G → M →ₗ[k] M) (ha : ∀ g h x, a (g * h) x = a g (a h x))
    (H : Subgroup G) [H.FiniteIndex] (c : G → M) (hc : ∀ g h, c (g * h) = c g + a g (c h))
    (b : M) (hb : ∀ h ∈ H, c h = a h b - b) : ∃ x : M, ∀ g, c g = a g x - x := by
  classical
  let d : G → M := fun g => c g - (a g b - b)
  have hd : ∀ g h, d (g * h) = d g + a g (d h) := by
    intro g h
    simp only [d, hc, ha, map_sub]
    abel
  have hd0 : ∀ h ∈ H, d h = 0 := fun h hh => by simp only [d, hb h hh, sub_self]
  have hdH : ∀ g g' : G, (QuotientGroup.leftRel H) g g' → d g = d g' := by
    intro g g' hgg
    rw [QuotientGroup.leftRel_apply] at hgg
    have : g' = g * (g⁻¹ * g') := by group
    rw [this, hd, hd0 _ hgg, map_zero, add_zero]
  let D : G ⧸ H → M := fun q => Quotient.liftOn' q d hdH
  have hD : ∀ (g : G) (q : G ⧸ H), D (g • q) = d g + a g (D q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H x => exact hd g x
  let _inst : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hn : ((Fintype.card (G ⧸ H) : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsum : ∀ g : G, ∑ q, D q = ((Fintype.card (G ⧸ H) : ℕ) : k) • d g + a g (∑ q, D q) := by
    intro g
    rw [← Equiv.sum_comp (MulAction.toPerm g) D]
    conv_rhs => rw [Equiv.sum_comp (MulAction.toPerm g) D]
    simp only [MulAction.toPerm_apply, hD, Finset.sum_add_distrib, map_sum, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  refine ⟨b - (((Fintype.card (G ⧸ H) : ℕ) : k))⁻¹ • ∑ q, D q, fun g => ?_⟩
  have h1 : d g = (((Fintype.card (G ⧸ H) : ℕ) : k))⁻¹ • (∑ q, D q - a g (∑ q, D q)) := by
    rw [← eq_sub_iff_add_eq.2 (hsum g).symm, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have h2 : c g = d g + (a g b - b) := by simp only [d]; abel
  rw [h2, h1, map_sub, map_smul, smul_sub]
  abel

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_tmul (g : G) (x : V) (b : B) :
    actVB PD ρ g (x ⊗ₜ[Qp] b) = ρ g x ⊗ₜ[Qp] PD.actB g b := rfl

theorem actVB_mul (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp only [actVB_tmul, map_mul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem crisCob_of_finiteIndex [CharZero LL] (H : Subgroup G) [H.FiniteIndex] (c : G → V)
    (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (b : V ⊗[Qp] B)
    (hb : ∀ h ∈ H, c h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h b - b) :
    ∃ x : V ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x :=
  coboundary_of_finiteIndex (actVB PD ρ) (actVB_mul PD ρ) H (fun g => c g ⊗ₜ[Qp] (1 : B))
    (fun g h => by simp only [hc, add_tmul, actVB_tmul, map_one]) b hb

end Generic

section Classes

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O]
    [Algebra O LL] [TopologicalSpace LL] (T : LocLat G Qp LL O)

theorem mem_H1fT_iff_res [CharZero LL] (H : Subgroup G) [H.FiniteIndex] (κ : LatticeCohomology T.L) :
    κ ∈ latticeFiniteCohomology PD T.L ↔ ∃ c : ↥(latticeCocycles (resLat T H)),
      (∃ x : T.V ⊗[Qp] B, ∀ h : ↥H,
        (c : ↥H → T.V) h ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ (h : G) x - x) ∧
      Submodule.Quotient.mk c = resH1 T H κ := by
  constructor
  · rintro ⟨z, ⟨-, -, x, hx⟩, rfl⟩
    exact ⟨⟨resFun T H z, resFun_Z1T T H z z.2⟩, ⟨x, fun h => hx (h : G)⟩, rfl⟩
  · rintro ⟨c, ⟨x, hx⟩, hc⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
    have hc' : (Submodule.Quotient.mk c : LatticeCohomology (resLat T H)) =
        Submodule.Quotient.mk ⟨resFun T H z, resFun_Z1T T H z z.2⟩ := hc
    obtain ⟨y, -, hy⟩ := (Submodule.Quotient.eq _).1 hc'
    refine ⟨z, ⟨z.2, z.2.1, ?_⟩, rfl⟩
    refine crisCob_of_finiteIndex PD T.ρ H z z.2.1.2 (x - y ⊗ₜ[Qp] (1 : B)) fun h hh => ?_
    have h1 : T.ρ h y - y = (c : ↥H → T.V) ⟨h, hh⟩ - (z : G → T.V) h := congrFun hy ⟨h, hh⟩
    have h2 : (z : G → T.V) h = (c : ↥H → T.V) ⟨h, hh⟩ - (T.ρ h y - y) := by rw [h1]; abel
    rw [h2, sub_tmul, sub_tmul, hx ⟨h, hh⟩, map_sub, actVB_tmul, map_one]
    abel

end Classes

theorem GKs_finiteIndex {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (n : ℕ)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) : W.GKs.FiniteIndex := by
  have h1 : W.GKs = (GlobalTheory.Cyc.Gj K W.s).subgroupOf (GK K) := by
    ext x
    rw [GlobalTheory.Cyc.mem_GKs_iff_mem_Gj, Subgroup.mem_subgroupOf]
  have h2 : (GlobalTheory.Cyc.Gj K W.s).FiniteIndex := by
    have hlp : l.Prime := Fact.out
    constructor
    rw [GlobalTheory.Cyc.Gj, ← IntermediateField.finrank_eq_fixingSubgroup_index,
      GlobalTheory.Cyc.finrank_Ks K W.s W.s_pos]
    have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
      FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
        (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
    exact (Nat.mul_pos Module.finrank_pos
      (Nat.mul_pos (Nat.sub_pos_of_lt hlp.one_lt) (pow_pos hlp.pos _))).ne'
  rw [h1]
  infer_instance

end GlobalTheory.NL.FiniteRestrictionH1f
end

