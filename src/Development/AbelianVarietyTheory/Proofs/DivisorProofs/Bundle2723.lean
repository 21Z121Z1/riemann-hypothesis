import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_iso_carries_sharp_points_to_conjugates : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) := by
  first | exact @GlobalTheory.Poinc.Sep.conj_sharp_points | exact GlobalTheory.Poinc.Sep.conj_sharp_points | (intros; apply GlobalTheory.Poinc.Sep.conj_sharp_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldFlagsConjugateByAutomorphism
section
open CategoryTheory AlgebraicGeometry GlobalTheory

namespace GlobalTheory.FlagTrans

private theorem exists_adapted_basis {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] {N : ℕ}
    (W : Fin (N + 1) → Submodule K V) (hr : ∀ i, Module.finrank K (W i) = i)
    (hle : ∀ i : Fin N, W i.castSucc ≤ W i.succ) (htop : W (Fin.last N) = ⊤) :
    ∃ b : Module.Basis (Fin N) K V, ∀ i, W i = Submodule.span K (b '' {k | (k : ℕ) < i}) := by
  have hlt (i : Fin N) : W i.castSucc < W i.succ := by
    refine lt_of_le_of_ne (hle i) fun h => ?_
    have h1 := hr i.castSucc
    rw [h, hr] at h1
    simp at h1
  choose v hv hv' using fun i => SetLike.exists_of_lt (hlt i)
  have key (i : Fin (N + 1)) : W i = Submodule.span K (v '' {k | (k : ℕ) < i}) := by
    induction i using Fin.induction with
    | zero =>
      have h0 := hr 0
      simp only [Fin.val_zero, Submodule.finrank_eq_zero] at h0
      simp [h0]
    | succ i ih =>
      have hs : {k : Fin N | (k : ℕ) < (i.succ : Fin (N + 1))} =
          insert i {k : Fin N | (k : ℕ) < (i.castSucc : Fin (N + 1))} := by
        ext k
        simp only [Fin.val_succ, Set.mem_setOf_eq, Fin.val_castSucc, Set.mem_insert_iff, Fin.ext_iff]
        omega
      rw [hs, Set.image_insert_eq, Submodule.span_insert, ← ih]
      have h1 : Submodule.span K {v i} ⊔ W i.castSucc ≤ W i.succ :=
        sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (hv i)) (hle i)
      have h2 : W i.castSucc < Submodule.span K {v i} ⊔ W i.castSucc := by
        refine lt_of_le_of_ne le_sup_right fun h => hv' i ?_
        rw [h]
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      have h3 := Submodule.finrank_lt_finrank_of_lt h2
      refine (Submodule.eq_of_le_of_finrank_le h1 ?_).symm
      rw [hr] at h3 ⊢
      simpa using h3
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← htop, key]
    exact Submodule.span_mono (Set.image_subset_range _ _)
  have hc : Fintype.card (Fin N) = Module.finrank K V := by
    have := hr (Fin.last N)
    rw [htop, finrank_top] at this
    simp [this]
  exact ⟨basisOfTopLeSpanOfCardEqFinrank v hsp hc, fun i => by
    rw [coe_basisOfTopLeSpanOfCardEqFinrank]; exact key i⟩

private theorem exists_equiv_of_chains {R V : Type} [CommRing R] (hR : IsField R) [AddCommGroup V] [Module R V] {N : ℕ}
    {A B : Fin (N + 1) → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module R (B i)] (f : ∀ i, A i →ₗ[R] V) (g : ∀ i, B i →ₗ[R] V)
    (hf : ∀ i, Function.Injective (f i)) (hg : ∀ i, Function.Injective (g i))
    (a : ∀ i : Fin (N + 1), Module.Basis (Fin i) R (A i)) (b : ∀ i : Fin (N + 1), Module.Basis (Fin i) R (B i))
    (hfle : ∀ i : Fin N, LinearMap.range (f i.castSucc) ≤ LinearMap.range (f i.succ))
    (hgle : ∀ i : Fin N, LinearMap.range (g i.castSucc) ≤ LinearMap.range (g i.succ))
    (hft : Function.Surjective (f (Fin.last N))) (hgt : Function.Surjective (g (Fin.last N))) :
    ∃ φ : V ≃ₗ[R] V, ∀ i, ∃ e : A i ≃ₗ[R] B i, ∀ s, g i (e s) = φ (f i s) := by
  letI := hR.toField
  haveI := Module.Finite.of_basis (a (Fin.last N))
  haveI : Module.Finite R V := Module.Finite.of_surjective _ hft
  obtain ⟨u, hu⟩ := exists_adapted_basis (K := R) (fun i => LinearMap.range (f i))
    (fun i => by rw [LinearMap.finrank_range_of_inj (hf i), Module.finrank_eq_card_basis (a i), Fintype.card_fin])
    hfle (LinearMap.range_eq_top.2 hft)
  obtain ⟨w, hw⟩ := exists_adapted_basis (K := R) (fun i => LinearMap.range (g i))
    (fun i => by rw [LinearMap.finrank_range_of_inj (hg i), Module.finrank_eq_card_basis (b i), Fintype.card_fin])
    hgle (LinearMap.range_eq_top.2 hgt)
  refine ⟨u.equiv w (Equiv.refl _), fun i => ?_⟩
  have hmap : (LinearMap.range (f i)).map (u.equiv w (Equiv.refl _) : V →ₗ[R] V) = LinearMap.range (g i) := by
    have h1 := hu i
    have h2 := hw i
    rw [h1, h2, Submodule.map_span, Set.image_image]
    simp
  refine ⟨(LinearEquiv.ofInjective (f i) (hf i)).trans (((u.equiv w (Equiv.refl _)).ofSubmodules _ _ hmap).trans
    (LinearEquiv.ofInjective (g i) (hg i)).symm), fun s => ?_⟩
  simp

variable {X : Scheme.{0}}

private theorem subsingleton_sections_bot (F : X.Modules) : Subsingleton Γ(F, ⊥) := by
  refine ⟨fun s t ↦ ?_⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (C := Ab.{0}) ⟨F.presheaf, F.isSheaf⟩
    (fun i : PEmpty.{1} ↦ i.elim) ⊥ (fun i ↦ i.elim) (by simp) s t (fun i ↦ i.elim)

private theorem eq_bot_or_top [Subsingleton X] (U : X.Opens) : U = ⊥ ∨ U = ⊤ := by
  rcases U.1.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact .inl (TopologicalSpace.Opens.ext h)
  · exact .inr (eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx)

private theorem hom_ext_top [Subsingleton X] {F G : X.Modules} {φ ψ : F ⟶ G}
    (h : ∀ s, φ.app ⊤ s = ψ.app ⊤ s) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  rcases eq_bot_or_top U with rfl | rfl
  · exact (subsingleton_sections_bot G).elim _ _
  · exact h s

private theorem exists_iso_top [Subsingleton X] {F G : X.Modules} {n : ℕ} {e : Fin n → Γ(F, ⊤)} (he : VB.IsFrame e)
    (g : Γ(F, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(G, ⊤)) : ∃ φ : F ≅ G, ∀ s, φ.hom.app ⊤ s = g s := by
  have he' : VB.IsFrame fun i => g (e i) := by
    intro V h
    rcases eq_bot_or_top V with rfl | rfl
    · haveI := subsingleton_sections_bot G
      haveI : Subsingleton Γ(X, ⊥) := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty rfl)
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    · have : Fintype.linearCombination Γ(X, ⊤) (fun i => Twist.resM G h (g (e i))) =
          g.toLinearMap ∘ₗ Fintype.linearCombination Γ(X, ⊤) (fun i => Twist.resM F h (e i)) := by
        refine LinearMap.ext fun a => ?_
        simp [Fintype.linearCombination_apply, Twist.resM_self]
      rw [this]
      exact g.bijective.comp (he ⊤ h)
  refine ⟨he.iso he', fun s => ?_⟩
  have : QCoh.appLinear (he.iso he').hom ⊤ = g.toLinearMap := by
    refine (he.basis le_rfl).ext fun i => ?_
    rw [VB.IsFrame.basis_apply, Twist.resM_self, QCoh.appLinear_apply]
    exact he.iso_hom_app he' i
  exact LinearMap.congr_fun this s

private theorem exists_frame_top [Subsingleton X] [Nonempty X] {F : X.Modules} {n : ℕ} (h : VB.IsVB F n) :
    ∃ e : Fin n → Γ(F, ⊤), VB.IsFrame e := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, e, hx, he⟩ := h x
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx
  exact ⟨e, he⟩

private theorem range_le {M : X.Modules} {N : ℕ} (F : Vert.Flag M N) (i : Fin N) :
    LinearMap.range (QCoh.appLinear (F.ι i.castSucc) ⊤) ≤ LinearMap.range (QCoh.appLinear (F.ι i.succ) ⊤) := by
  rintro _ ⟨s, rfl⟩
  refine ⟨(F.step i).app ⊤ s, ?_⟩
  rw [← F.step_ι i]
  rfl

end GlobalTheory.FlagTrans

open GlobalTheory.FlagTrans in
theorem _root_.GlobalTheory.T.field_flags_conjugate_by_automorphism : ∀ (L : Type) [Field L] (M : (Spec (CommRingCat.of L)).Modules) (N : ℕ) (F₁ F₂ : Vert.Flag M N), ∃ φ : M ≅ M, ∀ i, ∃ e : F₁.F i ≅ F₂.F i, e.hom ≫ F₂.ι i = F₁.ι i ≫ φ.hom := by
  intro L _ M N F₁ F₂
  have hR : IsField Γ(Spec (CommRingCat.of L), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField L)
  choose a ha using fun i => exists_frame_top (F₁.isVB i)
  choose b hb using fun i => exists_frame_top (F₂.isVB i)
  obtain ⟨m, hm⟩ := exists_frame_top F₁.isVB_self
  obtain ⟨g, hg⟩ := exists_equiv_of_chains hR (fun i => QCoh.appLinear (F₁.ι i) ⊤) (fun i => QCoh.appLinear (F₂.ι i) ⊤)
    (fun i => QCoh.injective_app_of_mono _ _) (fun i => QCoh.injective_app_of_mono _ _)
    (fun i => (ha i).basis le_rfl) (fun i => (hb i).basis le_rfl) (range_le F₁) (range_le F₂)
    (ConcreteCategory.bijective_of_isIso ((F₁.ι (Fin.last N)).app ⊤)).2
    (ConcreteCategory.bijective_of_isIso ((F₂.ι (Fin.last N)).app ⊤)).2
  obtain ⟨φ, hφ⟩ := exists_iso_top hm g
  refine ⟨φ, fun i => ?_⟩
  obtain ⟨e, he⟩ := hg i
  obtain ⟨ψ, hψ⟩ := exists_iso_top (ha i) e
  refine ⟨ψ, hom_ext_top fun s => ?_⟩
  change (F₂.ι i).app ⊤ (ψ.hom.app ⊤ s) = φ.hom.app ⊤ ((F₁.ι i).app ⊤ s)
  rw [hψ, hφ]
  exact he s
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinProdIsGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumSide

section Helpers
variable {X Y : Scheme.{0}} {L : LB X}

theorem exists_zpow (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => n * ε k)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact ⟨GeneratorPullback.powGen L φ ε t m, DVR.powGen_isGen _ _ _ _ ht m,
      fun Z r z J _ => (DVR.val_pow t m r z J).trans (zpow_natCast _ _).symm⟩
  · obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := fun k => -(m : ℤ) * ε k) (fun U _ h => by
        refine Finset.prod_congr rfl fun k _ => ?_
        show _ = h (φ k) ^ (-(m : ℤ) * ε k)
        rw [neg_mul]) (LB.invGen L _ _ (GeneratorPullback.powGen L φ ε t m))
        (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ ht m))
    refine ⟨t', ht', fun Z r z J hJ => ?_⟩
    rw [hv Z r z J hJ, val_inv, DVR.val_pow, zpow_neg, zpow_natCast]

theorem finProd_isGen {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) : (GeneratorPullback.finProdGen L φ ε t).IsGen := by
  intro (j : I × K → L.ι) (j' : I × K → L.ι)
  refine unit_ext fun y hy => ?_
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y (LB.wchart L (fun p : I × K => φ p.1 p.2) j) ((GeneratorPullback.finProdGen L φ ε t).s j) =
        ∏ i, gm (𝟙 Y) y (LB.wchart L (φ i) (fun k => j (i, k))) ((t i).s (fun k => j (i, k))) := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ => gm_res (𝟙 Y) y _ hj _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (𝟙 Y) y
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k)) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (i, k))

theorem val_finProd {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (GeneratorPullback.finProdGen L φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Helpers

section Rows
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem comp_tensφ' {S : Scheme.{0}} {B B' T : Over S} [GrpObj B] (pr : Fin r → (B' ⟶ B)) (x : T ⟶ B')
    (k : (Fin r × Fin r) × Fin 4) : x.left ≫ tensφ pr k = GlobalTheory.PolDeg.lamPts (x ≫ pr k.1.1) (x ≫ pr k.1.2) k.2 := by
  obtain ⟨⟨i, j⟩, k⟩ := k
  fin_cases k
  · exact congrArg (·.left) (MonObj.comp_mul x (pr i) (pr j))
  · rfl
  · rfl
  · exact congrArg (·.left) (MonObj.comp_one (M := B) x)

theorem matAct_zero (T : Tens D D' W) : GlobalTheory.TensAct.matAct T 0 = 1 := by
  have h := GlobalTheory.TensAct.matAct_add T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem four_eq (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A)
    (hf : f = GlobalTheory.TensAct.matAct T A) (a : Fin 4) :
    (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] :
      Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) a =
      (GlobalTheory.TensAct.matAct T ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a)).left := by
  subst hf
  fin_cases a
  · show (padd D'.P.A (𝟙 _) _).left = (GlobalTheory.TensAct.matAct T (1 + A)).left
    rw [GlobalTheory.TensAct.matAct_add, GlobalTheory.TensAct.matAct_one]; rfl
  · show 𝟙 D'.P.A.left = (GlobalTheory.TensAct.matAct T 1).left
    rw [GlobalTheory.TensAct.matAct_one]; rfl
  · rfl
  · show (toUnit D'.P.A ≫ η[D'.P.A]).left = (GlobalTheory.TensAct.matAct T 0).left
    rw [matAct_zero]; rfl

theorem sum_one_smul {X : Type} [AddCommGroup X] (v : Fin r → X) (i : Fin r) :
    ∑ k, (1 : Matrix (Fin r) (Fin r) ℤ) i k • v k = v i := by
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl.symm, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem xe_four (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) (a : Fin 4) (i : Fin r) :
    T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i =
      ∑ k, (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k • T.xe y k := by
  fin_cases a
  · show T.xe (y + GlobalTheory.TensAct.latAct T A y) i = ∑ k, (1 + A) i k • T.xe y k
    rw [map_add, Pi.add_apply, GlobalTheory.TensAct.xe_latAct]
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, sum_one_smul]
  · show T.xe y i = ∑ k, (1 : Matrix (Fin r) (Fin r) ℤ) i k • T.xe y k
    rw [sum_one_smul]
  · show T.xe (GlobalTheory.TensAct.latAct T A y) i = ∑ k, A i k • T.xe y k
    rw [GlobalTheory.TensAct.xe_latAct]
  · show T.xe 0 i = ∑ k, (0 : Matrix (Fin r) (Fin r) ℤ) i k • T.xe y k
    simp only [map_zero, Pi.zero_apply, Matrix.zero_apply, zero_smul, Finset.sum_const_zero]

end Rows

end GlobalTheory.MumSide
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEvenCubicalValuesNotMemMaximalIdealPowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_even_cubical_values_not_mem_maximalIdeal_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ n : ℕ, {a | ¬ ∃ s ∈ maximalIdeal R ^ n, (κ a : FractionRing R) = algebraMap R _ s}.Finite := by
  first | exact @GlobalTheory.QuadTend.finite_not_mem_pow | exact GlobalTheory.QuadTend.finite_not_mem_pow | (intros; apply GlobalTheory.QuadTend.finite_not_mem_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperPropertiesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_local_baseChange_of_proper_properties : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsFinite k ∧ QuasiCompact p' ∧ QuasiSeparated p' ∧ Function.Surjective k'.base ∧ IsClosedMap (p' ≫ k).base ∧ IsClosedMap p.base ∧ (∀ V : Y.Opens, IsAffineOpen V → IsCompact (p ⁻¹ᵁ V : Set Z) ∧ IsQuasiSeparated (p ⁻¹ᵁ V : Set Z)) ∧ ∃ (d : ℕ) (b : Fin d → R'), ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, ρ (c l) * b l := by
  first | exact @GlobalTheory.finiteFlat_proper_baseChange_facts | exact GlobalTheory.finiteFlat_proper_baseChange_facts | (intros; apply GlobalTheory.finiteFlat_proper_baseChange_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatUnitCocycleLocallyCoboundaryStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteFlat_unitCocycle_locally_coboundary : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
    (V : Y.Opens) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
    (∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c) →
    ∀ y ∈ V, ∃ V' : Y.Opens, V' ≤ V ∧ y ∈ V' ∧ ∃ u : Γ(X, f ⁻¹ᵁ V')ˣ,
      ∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u := by
  first | exact @GlobalTheory.LBDescent.coboundary_locally_of_cocycle | exact GlobalTheory.LBDescent.coboundary_locally_of_cocycle | (intros; apply GlobalTheory.LBDescent.coboundary_locally_of_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFractionFieldOfFinitelyManyProportionalIma
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LevelFinite.finite_of_isAlgebraic : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (K0 : Subfield Ω), R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → (∀ a : o, algebraMap o Ω a ∈ K0) → Algebra.IsAlgebraic K0 Ω → Module.Finite K0 Ω := by
  intro o Ω _ _ _ R K0 hfg hfrac ho halg
  obtain ⟨s, hs⟩ := hfg
  have hL : FiniteDimensional K0 (IntermediateField.adjoin K0 (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (halg.isAlgebraic x).isIntegral)
  have hR : ∀ a ∈ R, a ∈ IntermediateField.adjoin K0 (s : Set Ω) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K0 _ hx
    | algebraMap r => exact IntermediateField.algebraMap_mem _ (⟨_, ho r⟩ : K0)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have htop : IntermediateField.adjoin K0 (s : Set Ω) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, ha, c, hc, rfl⟩ := hfrac z
    exact div_mem (hR a ha) (hR c hc)
  rw [htop] at hL
  exact (IntermediateField.topEquiv (F := K0) (E := Ω)).toLinearEquiv.finiteDimensional

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  first
  | rfl
  | simp [spMap, ← Spec.map_comp]
  | (simp only [spMap]; rw [← Spec.map_comp]; rfl)

private theorem pow_injective_of_transcendental {Ω : Type} [Field Ω] (K0 : Subfield Ω) (z : Ω) (hz : Transcendental K0 z) :
    Function.Injective (fun m : ℕ => z ^ m) := by
  have h0 : z ≠ 0 := fun h => hz (h ▸ isAlgebraic_zero)
  have h1 : ∀ k : ℕ, 0 < k → z ^ k ≠ 1 := by
    intro k hk hzk
    apply hz
    refine ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero hk 1, ?_⟩
    simp [hzk]
  have key : ∀ m m' : ℕ, m < m' → z ^ m = z ^ m' → False := by
    intro m m' h hmm
    apply h1 (m' - m) (Nat.sub_pos_of_lt h)
    have : z ^ m * z ^ (m' - m) = z ^ m * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, hmm]
    exact mul_left_cancel₀ (pow_ne_zero _ h0) this
  intro m m' hmm
  simp only at hmm
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key m m' h hmm
  · exact key m' m h hmm.symm

theorem GlobalTheory.LevelFinite.finite_ratio_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (X : Scheme.{0}) (x : Sp R ⟶ X) (I : Type) [Finite I] (v : I → R), R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite → (∀ (K : Type) [Field K] [IsAlgClosed K] (c : I → K), Set.Finite {y : Sp K ⟶ X | ∃ σ : R →+* K, spMap σ ≫ x = y ∧ ∃ u : K, u ≠ 0 ∧ ∀ i, σ (v i) = u * c i}) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)})) Ω := by
  intro o Ω _ _ _ R X x I _ v hfg hfrac hfin hpts
  refine GlobalTheory.LevelFinite.finite_of_isAlgebraic o Ω R _ hfg hfrac
    (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)) ⟨fun z => ?_⟩
  by_contra hz
  obtain ⟨φ, hφ, hφeq⟩ := GlobalTheory.T.exists_finite_fieldEmbedding_stalk_of_finite_stalkMap Ω X (spMap R.val.toRingHom ≫ x) hfin
  have hτ : ∀ m : ℕ, ∃ τ : Ω →ₐ[Subfield.closure (Set.range (algebraMap o Ω) ∪
      {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)})] AlgebraicClosure Ω,
      τ z = algebraMap Ω (AlgebraicClosure Ω) z ^ (m + 1) :=
    fun m => GlobalTheory.T.exists_algHom_algebraicClosure_apply_eq_pow' Ω _ z hz (m + 1) m.succ_pos
  choose τ hτ using hτ
  have hfib : ∀ y : Sp (AlgebraicClosure Ω) ⟶ X,
      Set.Finite {τ' : Ω →+* AlgebraicClosure Ω | spMap τ' ≫ spMap R.val.toRingHom ≫ x = y} := by
    intro y
    by_cases hne : ∃ τ0 : Ω →+* AlgebraicClosure Ω, spMap τ0 ≫ spMap R.val.toRingHom ≫ x = y
    · obtain ⟨τ0, hτ0⟩ := hne
      refine (GlobalTheory.T.finite_setOf_ringHom_comp_eq_of_finite' _ Ω _ φ (τ0.comp φ) hφ).subset ?_
      intro τ' hτ'
      exact hφeq _ τ' τ0 (hτ'.trans hτ0.symm)
    · convert Set.finite_empty
      ext τ'
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hne ⟨τ', h⟩
  have hS := hpts (AlgebraicClosure Ω) (fun i => algebraMap Ω (AlgebraicClosure Ω) (v i))
  have hinj : Function.Injective (fun m : ℕ => ((τ m : Ω →ₐ[_] AlgebraicClosure Ω) : Ω →+* AlgebraicClosure Ω)) := by
    intro m m' hmm
    have h1 : τ m z = τ m' z := by
      simpa using congrArg (fun f : Ω →+* AlgebraicClosure Ω => f z) hmm
    rw [hτ, hτ, ← map_pow, ← map_pow] at h1
    exact Nat.succ_injective (pow_injective_of_transcendental _ z hz ((algebraMap Ω (AlgebraicClosure Ω)).injective h1))
  apply Set.infinite_range_of_injective hinj
  refine (hS.biUnion (fun y _ => hfib y)).subset ?_
  rintro _ ⟨m, rfl⟩
  refine Set.mem_biUnion (x := spMap ((τ m : Ω →+* AlgebraicClosure Ω)) ≫ spMap R.val.toRingHom ≫ x) ?_ rfl
  refine ⟨((τ m : Ω →+* AlgebraicClosure Ω)).comp R.val.toRingHom, by rw [spMap_comp_moduli_spaces, Category.assoc], ?_⟩
  by_cases h : ∃ i, (v i : Ω) ≠ 0
  · obtain ⟨i0, hi0⟩ := h
    have hc0 : algebraMap Ω (AlgebraicClosure Ω) (v i0) ≠ 0 := by
      exact (map_ne_zero _).mpr hi0
    have hτ0 : τ m (v i0) ≠ 0 := by
      exact (map_ne_zero _).mpr hi0
    refine ⟨τ m (v i0) / algebraMap Ω (AlgebraicClosure Ω) (v i0), div_ne_zero hτ0 hc0, fun i => ?_⟩
    have hr : (v i : Ω) / (v i0 : Ω) ∈ Subfield.closure (Set.range (algebraMap o Ω) ∪
        {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)}) := Subfield.subset_closure (Or.inr ⟨i, i0, rfl⟩)
    have hfix : τ m ((v i : Ω) / (v i0 : Ω)) = algebraMap Ω (AlgebraicClosure Ω) ((v i : Ω) / (v i0 : Ω)) := by
      have := (τ m).commutes ⟨_, hr⟩
      rw [IsScalarTower.algebraMap_apply _ Ω (AlgebraicClosure Ω)] at this
      exact this
    have key : τ m (v i) = τ m ((v i : Ω) / (v i0 : Ω)) * τ m (v i0) := by
      rw [← map_mul, div_mul_cancel₀ _ hi0]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (R.val.toRingHom (v i) : Ω) = v i from rfl, key, hfix, map_div₀]
    ring
  · push_neg at h
    refine ⟨1, one_ne_zero, fun i => ?_⟩
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
    rw [show (R.val.toRingHom (v i) : Ω) = v i from rfl, h i]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsPosCombinationDefiniteSumStatement
section
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N] (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ Y), (∀ j x y, γ j x y = γ j y x) → (∀ j y, 0 ≤ γ j y y) → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ (b : LinearMap.BilinForm ℤ Y) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → μ ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat | exact GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat | (intros; apply GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsAfterBaseChangeStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_exists_after_base_change : ∀ (B Y T : Scheme.{0}) (π : Y ⟶ B) (g : T ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∃ fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback (pullback.snd π g)).obj ((Scheme.Modules.pullback g).obj (E a))) (r a), IsFlagBundle (pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r fl' := by
  first | exact @GlobalTheory.FlagBaseChange.isFlagBundle_pullback_snd | exact GlobalTheory.FlagBaseChange.isFlagBundle_pullback_snd | (intros; apply GlobalTheory.FlagBaseChange.isFlagBundle_pullback_snd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleFamilyUniqueIsoStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_family_unique_iso : ∀ (B Y Y' : Scheme.{0}) (π : Y ⟶ B) (π' : Y' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (r a)), IsFlagBundle π E r fl → IsFlagBundle π' E r fl' → ∃ e : Y ≅ Y', e.hom ≫ π' = π := by
  first | exact @GlobalTheory.CovTest.flagBundle_iso_over | exact GlobalTheory.CovTest.flagBundle_iso_over | (intros; apply GlobalTheory.CovTest.flagBundle_iso_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFlagsUniqueFlagCoverPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagBundle_point_flags_unique_flagCover_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.FramesExist X → GlobalTheory.VarFlag.CarriesTri C → ∀ (K : Type) [Field K] (z z' : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C z' p → z = z' := by
  first | exact @GlobalTheory.VarFlag.rel_unique | exact GlobalTheory.VarFlag.rel_unique | (intros; apply GlobalTheory.VarFlag.rel_unique <;> assumption)
end

