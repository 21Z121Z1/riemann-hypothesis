import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0520
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeRingActionIffEndomorphismRelations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActRel

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def prodPow {r : ℕ} (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ) : A ⟶ A := ∏ k, f k ^ c k

theorem prodPow_add {r : ℕ} (f : Fin r → (A ⟶ A)) (c d : Fin r → ℤ) :
    prodPow f (c + d) = prodPow f c * prodPow f d := by
  simp [prodPow, zpow_add, Finset.prod_mul_distrib]

theorem prodPow_zero {r : ℕ} (f : Fin r → (A ⟶ A)) : prodPow f 0 = 1 := by
  simp [prodPow]

theorem prodPow_zsmul {r : ℕ} (f : Fin r → (A ⟶ A)) (n : ℤ) (c : Fin r → ℤ) :
    prodPow f (n • c) = prodPow f c ^ n := by
  simp [prodPow, zpow_mul', Finset.prod_zpow]

theorem prodPow_single {r : ℕ} (f : Fin r → (A ⟶ A)) (k : Fin r) : prodPow f (Pi.single k 1) = f k := by
  unfold prodPow
  rw [Finset.prod_eq_single k]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

def prodPowHom {r : ℕ} (f : Fin r → (A ⟶ A)) : Multiplicative (Fin r → ℤ) →* (A ⟶ A) :=
  MonoidHom.mk' (fun c => prodPow f c.toAdd) (fun c d => prodPow_add f c.toAdd d.toAdd)

theorem prodPow_sum {r : ℕ} (f : Fin r → (A ⟶ A)) {J : Type} (s : Finset J) (g : J → Fin r → ℤ) :
    prodPow f (∑ i ∈ s, g i) = ∏ i ∈ s, prodPow f (g i) := by
  have := map_prod (prodPowHom f) (fun i => Multiplicative.ofAdd (g i)) s
  rw [← ofAdd_sum] at this
  exact this

def precompHom (h : A ⟶ A) : (A ⟶ A) →* (A ⟶ A) :=
  MonoidHom.mk' (fun x => h ≫ x) (fun x y => MonObj.comp_mul h x y)

def postcompHom (h : A ⟶ A) [IsMonHom h] : (A ⟶ A) →* (A ⟶ A) :=
  MonoidHom.mk' (fun x => x ≫ h) (fun x y => MonObj.mul_comp x y h)

end GlobalTheory.ActRel

namespace GlobalTheory.ActRel

theorem prodPow_comp {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (f : Fin r → (A ⟶ A))
    (hf : ∀ k, IsMonHom (f k)) (cm : Fin r → Fin r → Fin r → ℤ) (hm : ∀ i j, f i ≫ f j = prodPow f (cm i j))
    (c d : Fin r → ℤ) :
    prodPow f c ≫ prodPow f d = prodPow f (∑ k, ∑ l, (c k * d l) • cm k l) := by
  haveI : IsMonHom (prodPow f d) := isMonHom_prodPow f hf d
  have h1 : prodPow f c ≫ prodPow f d = ∏ k, (f k ≫ prodPow f d) ^ c k := by
    have := map_prod (postcompHom (prodPow f d)) (fun k => f k ^ c k) Finset.univ
    refine this.trans (Finset.prod_congr rfl fun k _ => ?_)
    show (f k ^ c k) ≫ prodPow f d = _
    exact GrpObj.zpow_comp (f k) (c k) (prodPow f d)
  have h2 : ∀ k, f k ≫ prodPow f d = ∏ l, prodPow f (cm k l) ^ d l := by
    intro k
    have := map_prod (precompHom (f k)) (fun l => f l ^ d l) Finset.univ
    refine this.trans (Finset.prod_congr rfl fun l _ => ?_)
    show f k ≫ f l ^ d l = _
    rw [GrpObj.comp_zpow, hm]
  rw [h1, prodPow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h2, prodPow_sum, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [prodPow_zsmul, ← zpow_mul, mul_comm]

theorem ringAct_iff_relations : ∀ (O : Type) [Ring O] (r : ℕ) (e : Fin r → O),
    Submodule.span ℤ (Set.range e) = ⊤ → ∃ (m : ℕ) (N : Fin m → Fin r → ℤ) (c1 : Fin r → ℤ)
      (cm : Fin r → Fin r → Fin r → ℤ), ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
      (f : Fin r → (A ⟶ A)), (∀ k, IsMonHom (f k)) → ((∃ act : O → (A ⟶ A), IsRAct A act ∧ ∀ k, act (e k) = f k) ↔
        ((∀ j, ∏ k, f k ^ N j k = 1) ∧ ∏ k, f k ^ c1 k = 𝟙 A ∧
          ∀ i j, f i ≫ f j = ∏ k, f k ^ cm i j k)) := by
  intro O _ r e he
  let φ : (Fin r → ℤ) →ₗ[ℤ] O :=
    { toFun := fun c => ∑ k, c k • e k
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun n c => by simp [Finset.smul_sum, mul_smul] }
  have hφ : ∀ c, φ c = ∑ k, c k • e k := fun _ => rfl
  have hsurj : ∀ a, ∃ c, φ c = a := fun a => by
    have : a ∈ Submodule.span ℤ (Set.range e) := he ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp this
    exact ⟨c, hc⟩
  obtain ⟨m, N, hN⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (LinearMap.ker φ))
  choose coef hcoef using hsurj
  refine ⟨m, N, coef 1, fun i j => coef (e i * e j), ?_⟩
  intro S A _ _ f hf
  have hker : (∀ j, prodPow f (N j) = 1) → ∀ c ∈ LinearMap.ker φ, prodPow f c = 1 := by
    intro hNj c hc
    rw [← hN] at hc
    induction hc using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hNj j
    | zero => exact prodPow_zero f
    | add x y _ _ hx hy => rw [prodPow_add, hx, hy, _root_.mul_one]
    | smul n x _ hx => rw [prodPow_zsmul, hx, one_zpow]
  have hwd : (∀ j, prodPow f (N j) = 1) → ∀ c d, φ c = φ d → prodPow f c = prodPow f d := by
    intro hNj c d h
    have hcd : c - d ∈ LinearMap.ker φ := by simp [LinearMap.mem_ker, map_sub, h]
    calc prodPow f c = prodPow f (d + (c - d)) := by rw [add_sub_cancel]
      _ = prodPow f d := by rw [prodPow_add, hker hNj _ hcd, _root_.mul_one]
  have hmul : ∀ c d : Fin r → ℤ, φ c * φ d = ∑ k, ∑ l, (c k * d l) • (e k * e l) := by
    intro c d
    rw [hφ, hφ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_smul]
  constructor
  · rintro ⟨act, hact, hek⟩
    have h0 : act 0 = 1 := by
      have := hact.2.2.2 0 0
      rw [add_zero] at this
      exact mul_eq_left.mp this.symm
    let H : Multiplicative O →* (A ⟶ A) :=
      MonoidHom.mk' (fun a => act a.toAdd) (fun a b => hact.2.2.2 a.toAdd b.toAdd)
    have hact' : ∀ c, act (φ c) = prodPow f c := by
      intro c
      have : act (φ c) = H (Multiplicative.ofAdd (∑ k, c k • e k)) := rfl
      rw [this, ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [ofAdd_zsmul, map_zpow]
      show act (e k) ^ c k = _
      rw [hek]
    refine ⟨fun j => ?_, ?_, fun i j => ?_⟩
    · show prodPow f (N j) = 1
      have hNj : N j ∈ LinearMap.ker φ := hN ▸ Submodule.subset_span ⟨j, rfl⟩
      rw [← hact', LinearMap.mem_ker.mp hNj, h0]
    · show prodPow f (coef 1) = 𝟙 A
      rw [← hact', hcoef, hact.2.1]
    · show f i ≫ f j = prodPow f (coef (e i * e j))
      rw [← hact', hcoef, hact.2.2.1, hek, hek]
  · rintro ⟨hNj, h1, hm⟩
    refine ⟨fun a => prodPow f (coef a), ⟨fun a => isMonHom_prodPow f hf _, h1, fun a b => ?_, fun a b => ?_⟩,
      fun k => ?_⟩
    · rw [prodPow_comp f hf _ hm]
      apply hwd hNj
      rw [hcoef, map_sum]
      simp only [map_sum, map_zsmul, hcoef]
      rw [← hmul, hcoef, hcoef]
    · rw [← prodPow_add]
      apply hwd hNj
      rw [map_add, hcoef, hcoef, hcoef]
    · show prodPow f (coef (e k)) = f k
      rw [hwd hNj (coef (e k)) (Pi.single k 1) (by rw [hcoef, hφ]; simp [Pi.single_apply]),
        prodPow_single]

end GlobalTheory.ActRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotient
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.EtaleLie

variable {S : Scheme.{0}}

theorem fst_spMap_epsScaleR {R' : Type} [CommRing R'] (c : R') :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (epsScaleR c) =
      spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r

theorem existsUnique_dual_lift {R' : Type} [CommRing R'] {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B)
    [IsMonHom ψ] [Etale ψ.left] (x : Sp R' ⟶ S) (h : Sp (DualNumber R') ⟶ B.left)
    (hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ h = (1 : Over.mk x ⟶ B).left) :
    ∃! l : Sp (DualNumber R') ⟶ A.left,
      spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ l = (1 : Over.mk x ⟶ A).left ∧ l ≫ ψ.left = h := by
  let π : CommRingCat.of (DualNumber R') ⟶ CommRingCat.of R' :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber R', a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  refine GlobalTheory.existsUnique_lift_of_etale_of_surjective ψ.left π hπ hnil _ h ?_
  show (1 : Over.mk x ⟶ A).left ≫ ψ.left = spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ h
  rw [hh]
  exact congrArg (·.left) (MonObj.one_comp ψ)

theorem lie_of_etale : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (Ga : Type) [Group Ga] (ρ : Ga → (o.A.left ⟶ o.A.left)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover Ga ρ ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ A', IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A'), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b M S s o A' _ _ act' ψ Ga _ ρ _hab hψ hG hact
  haveI := hψ
  haveI : Etale ψ.left := hG.etale
  refine ⟨?_, ?_⟩
  · intro R' _ β x hx v hv
    obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := existsUnique_dual_lift ψ x v.left hv.1
    let u : epsPtR x ⟶ o.A := Over.homMk l (by
      show l ≫ o.A.hom = _
      rw [← Over.w ψ, ← Category.assoc, hl₂]; exact Over.w v)
    have hu : IsTanScal o.act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) u := by
      refine ⟨hl₁, ?_⟩
      have hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ (spMap (epsScaleR (β b.ρ)) ≫ v.left) =
          (1 : Over.mk x ⟶ A').left := by
        rw [← Category.assoc, fst_spMap_epsScaleR, hv.1]
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O D.ω)
      refine (existsUnique_dual_lift ψ x _ hh).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · show _ ≫ l ≫ (o.act.act _).left = _
        rw [← Category.assoc, hl₁]
        have e : ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O D.ω)).left = (1 : Over.mk x ⟶ o.A).left :=
          congrArg Over.Hom.left (MonObj.one_comp _)
        exact e
      · show (l ≫ (o.act.act _).left) ≫ ψ.left = _
        rw [Category.assoc, ← Over.comp_left, hact, Over.comp_left, ← Category.assoc, hl₂, ← hv.2]
        rfl
      · show _ ≫ spMap _ ≫ l = _
        rw [← Category.assoc, fst_spMap_epsScaleR, hl₁]
      · show (spMap _ ≫ l) ≫ ψ.left = _
        rw [Category.assoc, hl₂]
    obtain ⟨w, hw, hvw⟩ := o.lie R' β x hx u hu
    refine ⟨fun i => w i ≫ ψ, fun i c => ⟨?_, ?_⟩, ?_⟩
    · show _ ≫ (w i).left ≫ ψ.left = _
      rw [← Category.assoc, (hw i c).1]
      have e : ((1 : Over.mk x ⟶ o.A) ≫ ψ).left = (1 : Over.mk x ⟶ A').left :=
        congrArg Over.Hom.left (MonObj.one_comp ψ)
      exact e
    · show ((w i ≫ ψ) ≫ act'.act _).left = spMap _ ≫ (w i).left ≫ ψ.left
      rw [Category.assoc, ← hact, ← Category.assoc, Over.comp_left, (hw i c).2, Category.assoc]
    · apply Over.OverMorphism.ext
      rw [← GlobalTheory.LieEtale.ofFn_prod_comp ψ w, ← hvw]
      exact hl₂.symm
  · intro κ _ _ x β hx i
    exact (GlobalTheory.LieEtale.lieMult_iff_of_etale (𝓞 D.F) S o.A A' ψ (o.act.toF D) (act'.toF D) hψ hG.etale
      (fun c => hact _) κ x (β.comp (b.t i)) D.m).mp (o.lieRank κ x β hx i)

end GlobalTheory.UPel.HT.EtaleLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIteratedDerivHilbertEisensteinSplitLattice
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem hasSum_iterD_gval_split : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (u : List (Emb F)), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, lag k (u.count i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)) (iterD u (fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t u hk ha hτ
  obtain ⟨r, hr, hrad⟩ := GlobalTheory.T.exists_radius_moebius_perturbation_upperHalfPlane τ c t hτ
  obtain ⟨M, hM, hbd⟩ := GlobalTheory.T.exists_summable_bound_hilbert_eisenstein_terms F k 𝔞 𝔟 a₀ a x τ c t ha hτ
  set D : ℂ := ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k with hD
  set G : (Emb F → ℂ) → ℂ := fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) with hG
  have hcoord : ∀ z ∈ Metric.ball (0 : Emb F → ℂ) r, ∀ i, ‖z i‖ < r := fun z hz i ↦
    (norm_le_pi_norm z i).trans_lt (mem_ball_zero_iff.1 hz)
  have hne : ∀ w : ℂ, ‖w‖ < r → 1 + w * c ≠ 0 := fun w hw h ↦ by
    have := (hrad w hw).1
    rw [h, norm_zero] at this
    linarith
  have hψ : ∀ y : ℂ, DifferentiableOn ℂ (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) (Metric.ball 0 r) := by
    intro y w hw
    have h0 := hne w (mem_ball_zero_iff.1 hw)
    have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ 1 + w * c) w := by fun_prop
    have h2 : DifferentiableAt ℂ (fun w : ℂ ↦ y * w) w := by fun_prop
    exact (((h1.inv h0).pow k).mul (h2.div h1 h0).cexp).differentiableWithinAt
  have key := GlobalTheory.T.hasSum_iteratedComplexPartialDeriv_termwise (Emb F) F u r
    (fun ξ z ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c))))
    (fun z ↦ D⁻¹ * G z) M hr hM
    (fun ξ z hz ↦ by
      refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
      refine (HasFDerivAt.finset_prod (𝕜 := ℂ) (u := (Finset.univ : Finset (Emb F)))
        (g := fun i (z : Emb F → ℂ) ↦ (1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))
        (fun i _ ↦ DifferentiableAt.hasFDerivAt ?_)).differentiableAt
      have h1 := ((hψ ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (hcoord z hz i))))
      exact h1.comp z (differentiableAt_apply (𝕜 := ℂ) i z))
    (fun ξ z hz ↦ hbd ξ z (fun i ↦ hrad _ (hcoord z hz i)))
    (fun z hz ↦ by
      have := GlobalTheory.T.hasSum_hilbertEisenstein_movedPoint F k 𝔞 𝔟 a₀ a x τ c t z hk ha (fun i ↦ ⟨hne _ (hcoord z hz i), by
        have := (hrad _ (hcoord z hz i)).2
        linarith⟩)
      rw [div_eq_inv_mul] at this
      exact this)
  have hc := GlobalTheory.T.iteratedPartialDeriv_const_mul_reindex (Emb F) (Emb F) (Equiv.refl _) u G D⁻¹ 0
  simp only [Equiv.refl_symm, Equiv.coe_refl, id_eq, List.map_id, List.map_id_fun] at hc
  have hc' : iterD u (fun z ↦ D⁻¹ * G z) 0 = iterD u G 0 / D := by
    rw [div_eq_inv_mul]; exact hc
  rw [hc'] at key
  convert key using 2 with ξ
  have := GlobalTheory.T.iteratedPartialDeriv_prod_oneVar_at_zero (Emb F) u r
    (fun i w ↦ (1 + w * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * w / (1 + w * c)))
    (a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ)) hr
    (fun i ↦ hψ _)
  rw [this]
  congr 1
  exact Finset.prod_congr rfl (fun i _ ↦ (GlobalTheory.T.iteratedDeriv_zero_eq_laguerreDerivativePolynomialValue k _ c _).symm)

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubAFiniteFree
section
noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def heckeSubA {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (f : D.La →+ D.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • f x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add, smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

theorem mem_heckeSubA {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (f : D.La →+ D.La) (N : ℕ)
    (x : D.La) : o.eta (N • f x) ∈ heckeSubA o f N := ⟨x, rfl⟩

theorem eta_pow {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (n : ℕ) (z : D.La) :
    (o.eta z) ^ n = o.eta (n • z) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, eta_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, o.eta_add]

theorem pow_eq_one_of_mem {b : Base D R} {N k : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (f : D.La →+ D.La)
    (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ∈ heckeSubA o f N) : h ^ k = 1 := by
  obtain ⟨x, rfl⟩ := hh
  rw [eta_pow, smul_smul, show k * N = N * k from mul_comm _ _, o.eta_ker]

theorem act_mem {b : Base D R} {N k : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (f : D.La →+ D.La)
    (hf : ∀ (a : D.O) (x : D.La), ∃ z, f (a • x) = a • f x + (N * k) • z) (a : D.O)
    (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ∈ heckeSubA o f N) : h ≫ o.act.act a ∈ heckeSubA o f N := by
  obtain ⟨x, rfl⟩ := hh
  obtain ⟨z, hz⟩ := hf a x
  refine ⟨a • x, ?_⟩
  rw [hz, smul_add, o.eta_add, smul_smul, show N * (N * k) = (N * k) * N from mul_comm _ _, ← smul_smul,
    o.eta_ker, _root_.mul_one, ← o.eta_lin, smul_comm]

theorem heckeSubA_finite_free (b : Base D R) (f : D.La →+ D.La) (k N : ℕ) (hk : 0 < k) (hN : 0 < N)
    (hkp : k.Coprime p) (hNp : N.Coprime p) (s : S ⟶ Sp R) (o : Obj b (N * k) s) :
    Finite (heckeSubA o f N) ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A),
      h ∈ heckeSubA o f N → toUnit (Over.mk x) ≫ h = 1 → h = 1 := by
  refine ⟨?_, ?_⟩
  · haveI := D.finLa
    let K : Submodule ℤ D.La := LinearMap.range ((k : ℤ) • LinearMap.id)
    haveI : Finite (D.La ⧸ K) := by
      apply Module.finite_of_fg_torsion
      intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K q
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show (k : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, by simp⟩
    let σ := Function.surjInv (Submodule.Quotient.mk_surjective K)
    refine Finite.of_surjective
      (fun q : D.La ⧸ K => (⟨o.eta (N • f (σ q)), mem_heckeSubA o f N _⟩ : heckeSubA o f N)) ?_
    rintro ⟨h, x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, Subtype.ext ?_⟩
    have e : Submodule.Quotient.mk (σ (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk x : D.La ⧸ K) :=
      Function.surjInv_eq _ _
    rw [Submodule.Quotient.eq] at e
    obtain ⟨z, hz⟩ := e
    have hz' : σ (Submodule.Quotient.mk x) = x + k • z := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hz
      rw [hz]; abel
    show o.eta (N • f (σ (Submodule.Quotient.mk x))) = o.eta (N • f x)
    rw [hz', map_add, map_nsmul, smul_add, smul_smul, o.eta_add, o.eta_ker, _root_.mul_one]
  · intro κ _ _ x h hh h1
    obtain ⟨x0, rfl⟩ := hh
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
    obtain ⟨I, hI⟩ := o.geom κ x _ hβ
    have h2 : I.ev (N * k) (N • f x0) = 1 := by rw [← hI]; exact h1
    obtain ⟨y, hy⟩ := (I.ker (N * k) (Nat.mul_pos hN hk) (Nat.Coprime.mul hNp hkp) _).1 h2
    rw [hy, o.eta_ker]

example {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (N : ℕ) (h : 𝟙_ (Over S) ⟶ o.A)
    (hh : h ∈ heckeSubA o 0 N) : h = 1 := by
  obtain ⟨x, rfl⟩ := hh
  rw [AddMonoidHom.zero_apply, smul_zero, eta_zero]

end GlobalTheory.UPel.HT.HeckeAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubFiniteFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem heckeSub_finite_free : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), Finite (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A), h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N → toUnit (Over.mk x) ≫ h = 1 → h = 1 := by
  intro p _ D R _ b g k N hk hN hkp hNp S s o
  refine ⟨?_, ?_⟩
  · haveI := D.finLa
    let K : Submodule ℤ D.La := LinearMap.range ((k : ℤ) • LinearMap.id)
    haveI : Finite (D.La ⧸ K) := by
      apply Module.finite_of_fg_torsion
      intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K q
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show (k : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, by simp⟩
    let σ := Function.surjInv (Submodule.Quotient.mk_surjective K)
    refine Finite.of_surjective (fun q : D.La ⧸ K => (⟨o.eta (N • g (σ q)), mem_heckeSub o g N _⟩ : heckeSub o g N)) ?_
    rintro ⟨h, x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, Subtype.ext ?_⟩
    have e : Submodule.Quotient.mk (σ (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk x : D.La ⧸ K) :=
      Function.surjInv_eq _ _
    rw [Submodule.Quotient.eq] at e
    obtain ⟨z, hz⟩ := e
    have hz' : σ (Submodule.Quotient.mk x) = x + k • z := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hz
      rw [hz]; abel
    show o.eta (N • g (σ (Submodule.Quotient.mk x))) = o.eta (N • g x)
    rw [hz', map_add, map_nsmul, smul_add, smul_smul, o.eta_add, o.eta_ker, _root_.mul_one]
  · intro κ _ _ x h hh h1
    obtain ⟨x0, rfl⟩ := hh
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
    obtain ⟨I, hI⟩ := o.geom κ x _ hβ
    have h2 : I.ev (N * k) (N • g x0) = 1 := by rw [← hI]; exact h1
    obtain ⟨y, hy⟩ := (I.ker (N * k) (Nat.mul_pos hN hk) (Nat.Coprime.mul hNp hkp) _).1 h2
    rw [hy, o.eta_ker]

end GlobalTheory.UPel.HT.Hecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImagQuadIntegerLatticeMulStableISqrtStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imagQuadIntegerLattice_mulStable_I_sqrt : ∀ (d : ℕ) (Λ : PeriodPair), 0 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → MulStable Λ (Complex.I * (Real.sqrt d : ℝ)) ∧ (Complex.I * (Real.sqrt d : ℝ)).im ≠ 0 := by
  first | exact @GlobalTheory.IntLatMul.main | exact GlobalTheory.IntLatMul.main | (intros; apply GlobalTheory.IntLatMul.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdeleTranslateIntegralAdditiveTotalPropertiesStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties : ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ), (∀ x x' y y' : K, Tr t x x' → Tr t y y' → Tr t (x - y) (x' - y')) ∧ (∀ (a x x' : K), IsIntegral ℤ a → Tr t x x' → Tr t (a * x) (a * x')) ∧ (∀ x : K, ∃ x', Tr t x x') ∧ (∀ x' : K, ∃ x, Tr t x x') := by
  first | exact @GlobalTheory.WpFam.TrAdd.main | exact GlobalTheory.WpFam.TrAdd.main | (intros; apply GlobalTheory.WpFam.TrAdd.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerVanishingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_etale_vanishing : GlobalTheory.EtC.B6h1 := by
  first | (exact @GlobalTheory.EtC.kummer_vanishing) | (exact GlobalTheory.EtC.kummer_vanishing) | (intros; apply GlobalTheory.EtC.kummer_vanishing  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCorrespondenceTorsionRelationPropertiesStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCorrespondence_torsion_relation_properties : ∀ (K : Type) [Field K] [CharZero K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTr ι Λ₀ Λ₁ T → IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop), (∀ x y, R x y ↔ ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ y ∧ T k k') → (∀ x, ∃ y, R x y) ∧ (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) ∧ (∀ x y, R x y → (x = 0 ↔ y = 0)) := by
  first | exact @GlobalTheory.RelTors.main | exact GlobalTheory.RelTors.main | (intros; apply GlobalTheory.RelTors.main <;> assumption)
end

