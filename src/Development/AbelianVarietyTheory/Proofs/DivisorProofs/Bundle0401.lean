import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0316
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0002
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0381
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAW
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem Pair.cup_spec_full : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m), ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
  fun _ _ _ _ _ μ E _ _ _ hk => ⟨fun α β => μ.aw_exists E hk α β, fun α β γ h => μ.cup_spec E hk α β γ h⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullback
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

namespace CupPull

theorem sub_map {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.map f).sub j l h = (x.sub j l h).map f := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op U)) x
  simp only [NatTrans.comp_app, types_comp_apply, ConcreteCategory.comp_apply] at this
  exact this.symm

theorem isAW_pull {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) {α : Cochain ((chains R).obj E') I n} {β : Cochain ((chains R).obj E') J m}
    {γ : Cochain ((chains R).obj E') K k} (h : μ.IsAW hk α β γ) :
    μ.IsAW hk ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp β (zero_add m))
      ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add k)) := by
  intro N w hw U x
  rw [CupSpec.ev_pull, h N w hw U (x.map f)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [CupSpec.ev_pull, CupSpec.ev_pull, sub_map, sub_map]

end CupPull

theorem Pair.cup_pull : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) a b, cpull ((chains R).map f) K k (μ.cup E' hk a b) =
      μ.cup E hk (cpull ((chains R).map f) I n a) (cpull ((chains R).map f) J m b) := by
  intro R _ I J K μ E E' f n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := Pair.aw_exists μ E' hk α β
  rw [Pair.cup_spec μ E' hk α β γ hγ, cpre_mk, cpre_mk, cpre_mk]
  refine (Pair.cup_spec μ E hk _ _ _ ?_).symm
  have e : ((Cocycle.ofHom ((chains R).map f) : Cocycle _ _ 0) : Cochain _ _ 0) = Cochain.ofHom ((chains R).map f) :=
    Cocycle.ofHom_coe _
  simp only [zcomp, Cocycle.mk_coe, e]
  exact CupPull.isAW_pull μ f hk hγ

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegZeroCocycleExistsCoboundaryOfRichBased
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts.DegZero

theorem sub_rel {M : Type} [AddCommGroup M] {p0 p1 u0 u1 v0 v1 w z0 z1 : M}
    (c0 : p0 = u0 + w) (c0' : p0 = v0 + z0) (c1 : p1 = u1 + w) (c1' : p1 = v1 + z1) :
    u0 - u1 = v0 - v1 + (z0 - z1) := by
  have e0 : u0 = v0 + z0 - w := eq_sub_of_add_eq (c0.symm.trans c0')
  have e1 : u1 = v1 + z1 - w := eq_sub_of_add_eq (c1.symm.trans c1')
  rw [e0, e1]; abel

theorem sub_sub_eq_of_sub_eq_addCommGroup {M : Type} [AddCommGroup M] {h0 h1 j0 j1 d X : M}
    (e : h0 - h1 = d) (e' : j1 - j0 = d) : h0 - (X - j0) = h1 - (X - j1) := by
  have a0 : h0 = d + h1 := eq_add_of_sub_eq e
  have a1 : j1 = d + j0 := eq_add_of_sub_eq e'
  rw [a0, a1]; abel

theorem eq_inr {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    (x : TrivSqZeroExt O M) (hx : x.fst = 0) : x = TrivSqZeroExt.inr x.snd :=
  TrivSqZeroExt.ext hx rfl

theorem tszeSec_sub_inl {g : ℕ} {O : Type} [CommRing O] [Algebra ℂ O] (D : Fin g → Derivation ℂ O O) (x : O) :
    tszeSec D x - TrivSqZeroExt.inl x = TrivSqZeroExt.inr fun a ↦ D a x := by
  show TrivSqZeroExt.inl x + TrivSqZeroExt.inr (fun a ↦ D a x) - TrivSqZeroExt.inl x = _
  abel

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}

theorem translationChartShiftSubstitution_comp_degZero {k k' k'' : K.K} (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k)
    (f : Hol (K.W k)) : sh e' (sh e f) = sh e'' f :=
  Hol.ext_fn fun p hp ↦ by
    rw [fn_sh e' _ hp, fn_sh e _ (K.maps e' p hp), fn_sh e'' _ hp]
    simp only [F.shift_zero]

theorem ptHom_refl_triv (k : K.K) : ptHom (K.triv k) (K.le_refl k) = 𝟙 (K.triv k) :=
  hom_ext (fun c ↦ sh_refl (K.le_refl k) c) rfl

theorem ptHom_comp0 {k k' k'' : K.K} (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k) :
    ptHom (K.triv k') e ≫ ptHom (K.triv k'') e' = ptHom (K.triv k'') e'' :=
  hom_ext (fun c ↦ translationChartShiftSubstitution_comp_degZero e e' e'' c) (add_zero (0 : Λ))

def corr (h : C1 K.Oc) (G : C0 K.Oc) : C1 K.Oc := fun T T' φ ↦ h T T' φ - (G T' - φ.φ (G T))

theorem zero_id (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (T : K.Obj) : h T T (𝟙 T) = 0 := by
  have e := hc T T T (𝟙 T) (𝟙 T) rfl rfl
  rw [Category.id_comp] at e
  change (h T T (𝟙 T) : T.C) = h T T (𝟙 T) + h T T (𝟙 T) at e
  exact (add_eq_left.mp e.symm)

theorem corr_cocycle (h : C1 K.Oc) (G : C0 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) :
    ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      corr h G T T'' (φ ≫ ψ) = ψ.φ (corr h G T T' φ) + corr h G T' T'' ψ := by
  intro T T' T'' φ ψ hφ hψ
  change (h T T'' (φ ≫ ψ) : T''.C) - (G T'' - ψ.φ (φ.φ (G T))) =
    ψ.φ ((h T T' φ : T'.C) - (G T' - φ.φ (G T))) + ((h T' T'' ψ : T''.C) - (G T'' - ψ.φ (G T')))
  rw [hc T T' T'' φ ψ hφ hψ, map_sub, map_sub]
  abel

theorem vanish (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ)
    (v1 : ∀ T : K.Obj, h _ _ (ptHom T (K.le_refl T.k)) = 0)
    (v2 : ∀ k k' (e : K.le 0 k' k), h _ _ (ptHom (K.triv k') e) = 0)
    (v3 : ∀ k, h _ _ (jet0 k) = h _ _ (jet1 k)) (T T' : K.Obj) (φ : T ⟶ T') (hφ : φ.deg = 0) :
    h T T' φ = 0 := by
  have hm := GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism K h 0 (fun k T χ hχ ↦ by
    rw [hc _ _ _ (jet0 k) χ rfl hχ, hc _ _ _ (jet1 k) χ rfl hχ, v3 k])
  have v5 : ∀ (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T), f.deg = 0 → h _ _ f = 0 := by
    intro k T f hd
    have e : K.le 0 T.k k := hd ▸ Charts.Hom.le f
    have hs : ∀ c : Hol (K.W k), sh (Charts.Hom.le f) c = sh (K.le_refl T.k) (sh e c) := fun c ↦ by
      rw [sh_refl]
      exact Hol.ext_fn fun p hp ↦ by rw [fn_sh (Charts.Hom.le f) c hp, fn_sh e c hp, hd]
    have hcomp : ptHom T (Charts.Hom.le f) = ptHom (K.triv T.k) e ≫ ptHom T (K.le_refl T.k) :=
      hom_ext (fun c ↦ congrArg T.ρ (hs c)) (hd.trans (add_zero (0 : Λ)).symm)
    rw [hm k T f hd, hcomp, hc _ _ _ _ _ rfl rfl, v2, v1, map_zero, add_zero]
  have e := hc _ _ _ (ptHom T (K.le_refl T.k)) φ rfl hφ
  rw [v5 _ _ _ ((zero_add φ.deg).trans hφ), v1, map_zero, zero_add] at e
  exact e.symm

def jetDiff (h : C1 K.Oc) (k : K.K) : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) :=
  h _ _ (jet0 k) - h _ _ (jet1 k)

def trans0 (h : C1 K.Oc) (k k' : K.K) (e : K.le 0 k' k) : Hol (K.W k') := h _ _ (ptHom (K.triv k') e)

theorem jetDiff_sh (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k k' : K.K) (e : K.le 0 k' k) (i : Fin g) :
    (jetDiff h k').snd i - sh e ((jetDiff h k).snd i) = dw i (trans0 h k k' e) := by
  obtain ⟨χ, hχ, h0, h1, hx⟩ := GlobalTheory.T.exists_jet_morphism_extending_translation K e
  have c0 := hc _ _ _ (jet0 k) χ rfl hχ
  have c1 := hc _ _ _ (jet1 k) χ rfl hχ
  rw [h0] at c0
  rw [h1] at c1
  have key := sub_rel c0 (hc _ _ _ (ptHom (K.triv k') e) (jet0 k') rfl rfl) c1
    (hc _ _ _ (ptHom (K.triv k') e) (jet1 k') rfl rfl)
  have key' : χ.φ (jetDiff h k) = (jet0 k').φ (trans0 h k k' e) - (jet1 k').φ (trans0 h k k' e) + jetDiff h k' :=
    (map_sub χ.φ _ _).trans key
  have s := (hx (jetDiff h k)).2 i
  rw [key'] at s
  have s' : (0 : Hol (K.W k')) - (tszeSec (g := g) dw (trans0 h k k' e)).snd i + (jetDiff h k').snd i =
      sh e ((jetDiff h k).snd i) := s
  rw [snd_tszeSec] at s'
  rw [← s']
  abel

def gauge (h : C1 K.Oc) (G₀ : ∀ k, Hol (K.W k)) : C0 K.Oc :=
  fun T ↦ (T.ρ (G₀ T.k) + (h _ _ (ptHom T (K.le_refl T.k)) : T.C) : T.C)

theorem exists_gauge : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∃ G : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → h T T' φ = G T' - φ.φ (G T) := by
  intro I _ g Λ _ F K hR hB h hc
  have hcl := fun k ↦ GlobalTheory.T.connectionForm_degZeroCocycle_closed K h hc k (jetDiff h k) rfl
  obtain ⟨G₀, hd, ha⟩ := GlobalTheory.T.exists_primitive_cech_poincare_rich_charts K hR hB (trans0 h) (fun k ↦ (jetDiff h k).snd)
    (fun k k' k'' e e' e'' ↦ by
      have c := hc _ _ _ (ptHom (K.triv k') e) (ptHom (K.triv k'') e') rfl rfl
      rw [ptHom_comp0 e e' e''] at c
      exact c)
    (fun k i j ↦ (hcl k).2 i j) (jetDiff_sh h hc)
  have gt : ∀ k, gauge h G₀ (K.triv k) = G₀ k := fun k ↦ by
    have z : h _ _ (ptHom (K.triv k) (K.le_refl k)) = 0 := by
      rw [ptHom_refl_triv]; exact zero_id h hc _
    exact (congrArg (fun x : Hol (K.W k) ↦ G₀ k + x) z).trans (add_zero _)
  refine ⟨gauge h G₀, fun T T' φ hφ ↦ sub_eq_zero.mp
    (vanish (corr h (gauge h G₀)) (corr_cocycle h _ hc) (fun T ↦ ?_) (fun k k' e ↦ ?_) (fun k ↦ ?_) T T' φ hφ)⟩
  · have z : (ptHom T (K.le_refl T.k)).φ (gauge h G₀ (K.triv T.k)) = T.ρ (G₀ T.k) := by
      rw [gt]; exact congrArg T.ρ (sh_refl (K.le_refl T.k) _)
    unfold corr
    rw [z]
    exact sub_eq_zero.mpr (add_sub_cancel_left (G := T.C) _ _).symm
  · unfold corr
    rw [gt, gt]
    exact sub_eq_zero.mpr (ha k k' e)
  · unfold corr
    rw [gt]
    refine sub_sub_eq_of_sub_eq_addCommGroup (d := TrivSqZeroExt.inr (jetDiff h k).snd) (eq_inr (jetDiff h k) (hcl k).1) ?_
    have z0 : (jet0 k).φ (G₀ k) = TrivSqZeroExt.inl (G₀ k) :=
      congrArg TrivSqZeroExt.inl (sh_refl (K.le_refl k) (G₀ k))
    rw [z0]
    exact (tszeSec_sub_inl dw (G₀ k)).trans (congrArg TrivSqZeroExt.inr (funext (hd k)))

end GlobalTheory.AnPer.Charts.DegZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthGeThreeFiniteEtalePuncturedRegular
section
open IsLocalRing

namespace GlobalTheory.LocalLefschetz

lemma two_le_of_add_one {x y : WithBot ℕ∞} (h : x + 1 = y) (hy : 3 ≤ y) : 2 ≤ x := by
  subst h
  induction x using WithBot.recBotCoe with
  | bot => simp at hy
  | coe n =>
    have h3 : (3 : ℕ∞) ≤ n + 1 := WithBot.coe_le_coe.mp hy
    have : (2 : ℕ∞) ≤ n := by
      induction n using ENat.recTopCoe with
      | top => simp
      | coe m =>
        have : (3 : ℕ) ≤ m + 1 := by exact_mod_cast h3
        exact_mod_cast (by omega : 2 ≤ m)
    exact WithBot.coe_le_coe.mpr this

theorem depth_three : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ∉ maximalIdeal R ^ 2 → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], GlobalTheory.PurityFree (R ⧸ Ideal.span {f}) → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ReciprocityTheory.CA.ModDepthGE R A 3 := by
  intro R _ _ hcomp hdim f hf hf2 _ hpur A _ _ _ hdep hEt
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf2 (Ideal.zero_mem _)
  haveI : IsDomain R := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain R
  have hreg : IsSMulRegular A f :=
    GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' R A (ReciprocityTheory.CA.ModDepthGE.mono (by norm_num) hdep) hEt f hf0
  haveI hRb : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hf hf2
  have hdimb : 2 ≤ ringKrullDim (R ⧸ Ideal.span {f}) :=
    two_le_of_add_one
      (ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hf hf2) hdim
  haveI : Module.Finite R (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R ((Ideal.span {f}).map (algebraMap R A))).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hdepb := GlobalTheory.modDepthGE_quotient_map_span_singleton R A f hf hreg 1 hdep
  have hEtb := GlobalTheory.T.etale_quotient_of_etale_punctured' R A f hEt
  obtain ⟨A', _, _, hA'fin, ι, hι, hdep', hEt', k, hk⟩ := GlobalTheory.T.exists_finite_depth_two_hull_of_etale_punctured_spectrum _ hdimb _ hdepb hEtb
  have hfree : Module.Free (R ⧸ Ideal.span {f}) A' := hpur A' hdep' hEt'
  obtain ⟨_, _⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (R ⧸ Ideal.span {f})
  have hnf : ¬ IsField (R ⧸ Ideal.span {f}) := by
    intro hF
    have := ringKrullDim_eq_zero_of_isField hF
    rw [this] at hdimb
    exact absurd hdimb (by decide)
  have hEtA' : Algebra.Etale (R ⧸ Ideal.span {f}) A' := by
    refine GlobalTheory.T.etale_of_etale_at_height_one_primes _ A' hnf fun p _ hp => hEt' p ?_
    rintro rfl
    have h1 := maximalIdeal_height_eq_ringKrullDim (R := R ⧸ Ideal.span {f})
    rw [hp] at h1
    rw [← h1] at hdimb
    exact absurd hdimb (by decide)
  obtain ⟨B, _, _, hBfin, hBfree, hBet, ⟨e⟩⟩ := GlobalTheory.T.exists_finite_free_etale_lift_of_quotient_etale R hcomp f hf A'
  let φ : A →ₐ[R] B ⧸ (Ideal.span {f}).map (algebraMap R B) :=
    { toRingHom := e.symm.toRingHom.comp (ι.toRingHom.comp (Ideal.Quotient.mk _))
      commutes' := fun r => by
        have h1 : (Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R A)) (algebraMap R A r)) =
            algebraMap (R ⧸ Ideal.span {f}) _ (algebraMap R (R ⧸ Ideal.span {f}) r) := by
          rw [← IsScalarTower.algebraMap_apply]; rfl
        show e.symm (ι (Ideal.Quotient.mk _ (algebraMap R A r))) = _
        rw [h1, ι.commutes, e.symm.commutes, ← IsScalarTower.algebraMap_apply] }
  have hφ : ∀ a, φ a = e.symm (ι (Ideal.Quotient.mk _ a)) := fun a => rfl
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_lift_algHom_of_etale_punctured R hcomp hdim f hf hf0 A hEt B φ
  have hψa : ∀ a, Ideal.Quotient.mk _ (ψ a) = φ a := fun a => by
    rw [← hψ]; rfl
  have hBreg : IsSMulRegular B f := fun x y h => smul_right_injective B hf0 h
  have hsat : ∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) →
      a ∈ (Ideal.span {f}).map (algebraMap R A) := by
    intro a ha
    have h1 : φ a = 0 := by
      rw [← hψa]; exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [hφ] at h1
    have h2 : ι (Ideal.Quotient.mk _ a) = 0 := by
      simpa using h1
    have h3 : Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R A)) a = 0 :=
      hι (by rw [h2, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  obtain ⟨hinj, hfsat⟩ := GlobalTheory.T.injective_and_saturated_of_injective_mod_regular' R A B f hf hBreg ψ hsat
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {f})) ≤ maximalIdeal (R ⧸ Ideal.span {f}) := by
    rw [Ideal.map_le_iff_le_comap]
    have : (maximalIdeal (R ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal R := by
      haveI := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
        Ideal.Quotient.mk_surjective (K := maximalIdeal (R ⧸ Ideal.span {f}))
      exact IsLocalRing.eq_maximalIdeal this
    rw [this]
  have hspan : ∀ z : B, z ∈ (Ideal.span {f}).map (algebraMap R B) → ∃ c : B, z = f • c := by
    intro z hz
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hz
    obtain ⟨c, hc⟩ := hz
    exact ⟨c, by rw [Algebra.smul_def, ← hc, mul_comm]⟩
  have hcok : ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c := by
    refine ⟨k, fun x hx b => ?_⟩
    have hx' : Ideal.Quotient.mk (Ideal.span {f}) x ∈ maximalIdeal (R ⧸ Ideal.span {f}) ^ k := by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {f})) hx
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono hmap k this
    obtain ⟨abar, habar⟩ := hk _ hx' (e (Ideal.Quotient.mk _ b))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective abar
    refine ⟨a, ?_⟩
    have h1 : Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R B)) (x • b - ψ a) = 0 := by
      rw [map_sub, hψa, hφ]
      change Ideal.Quotient.mk _ (x • b) - e.symm (ι (Ideal.Quotient.mk _ a)) = 0
      have habar' : ι (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk (Ideal.span {f}) x • e (Ideal.Quotient.mk _ b) := habar
      have h2 : ∀ z, e.symm (Ideal.Quotient.mk (Ideal.span {f}) x • e z) =
          Ideal.Quotient.mk (Ideal.span {f}) x • z := fun z => by
        rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, AlgEquiv.symm_apply_apply, ← Algebra.smul_def]
      rw [habar', h2]
      change Ideal.Quotient.mkₐ R _ (x • b) - _ = 0
      rw [map_smul, ← algebraMap_smul (R ⧸ Ideal.span {f}) x, Ideal.Quotient.algebraMap_eq]
      exact sub_eq_zero.mpr rfl
    obtain ⟨c, hc⟩ := hspan _ (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    exact ⟨c, by rw [← hc]; abel⟩
  have hdim1 : 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) := le_trans (by decide) hdimb
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.cokernel_torsion_of_finiteLength_mod_element R f hdim1 A B ψ hcok
  have hEtB : ∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B) :=
    fun p _ _ => inferInstance
  obtain ⟨k2, hk2⟩ := GlobalTheory.T.finiteLength_coker_of_etale_punctured_spectrum R A B hEt hEtB ψ hinj ⟨s, hs0, hs⟩
  have hdesc : ∀ (n : ℕ) (b : B), f ^ n • b ∈ ψ.range → b ∈ ψ.range := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      apply ih
      apply hfsat
      rwa [← mul_smul, ← pow_succ']
  have hsurj : Function.Surjective ψ := fun b => by
    obtain ⟨a, ha⟩ := hdesc k2 b (hk2 _ (Ideal.pow_mem_pow hf k2) b)
    exact ⟨a, ha⟩
  let eqv : A ≃ₐ[R] B := AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  haveI : Module.Free R A := Module.Free.of_equiv eqv.symm.toLinearEquiv
  haveI : Nontrivial A := by
    obtain ⟨rs, -, -, hr⟩ := hdep
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hr.top_ne_smul (Subsingleton.elim _ _)
  exact GlobalTheory.T.modDepthGE_three_of_free_regularLocal R hdim A

end GlobalTheory.LocalLefschetz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAt0EqSumOfSubset
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem derivAt0_eq_sum_of_subset {C : Type} [Field C] {σ : Type} (P : MvPolynomial σ C)
    (g : MvPowerSeries σ C) {s : Finset (σ →₀ ℕ)} (hs : P.support ⊆ s) :
    derivAt0 P g = ∑ α ∈ s, P.coeff α * mfact α * coeff α g := by
  unfold derivAt0
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [MvPolynomial.notMem_support_iff.mp hα]
  simp

theorem derivAt0_linear (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (σ : Type) (P Q : MvPolynomial σ C) (g g' : MvPowerSeries σ C) (a : C) :
    derivAt0 P (g + g') = derivAt0 P g + derivAt0 P g' ∧
      derivAt0 P (a • g) = a * derivAt0 P g ∧
      derivAt0 (P + Q) g = derivAt0 P g + derivAt0 Q g ∧
      derivAt0 (a • P) g = a * derivAt0 P g ∧
      ((∀ α ∈ P.support, coeff α g = coeff α g') → derivAt0 P g = derivAt0 P g') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold derivAt0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_add, mul_add]
  · unfold derivAt0
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_smul, smul_eq_mul]
    ring
  · classical
    rw [derivAt0_eq_sum_of_subset (P + Q) g (MvPolynomial.support_add (p := P) (q := Q)),
      derivAt0_eq_sum_of_subset P g (Finset.subset_union_left (s₂ := Q.support)),
      derivAt0_eq_sum_of_subset Q g (Finset.subset_union_right (s₁ := P.support)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_add]
    ring
  · rw [derivAt0_eq_sum_of_subset (a • P) g (MvPolynomial.support_smul (a := a) (f := P)),
      derivAt0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    ring
  · intro h
    unfold derivAt0
    exact Finset.sum_congr rfl fun α hα => by rw [h α hα]

end GlobalTheory.FGDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetOneSubOffDiagonalBlockGramLeOneBall
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.DetLe

theorem re_det_one_sub_le_of_unique {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι] [Unique ι]
    (Z : Matrix κ ι ℂ) : ((1 - Zᴴ * Z).det).re ≤ 1 := by
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.sub_re, Complex.one_re, Complex.re_sum]
  have : ∀ a : κ, 0 ≤ (star (Z a default) * Z a default).re := by
    intro a
    rw [show star (Z a default) = (starRingEnd ℂ) (Z a default) from rfl, mul_comm, Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  linarith [Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) => this a]

theorem re_det_one_sub_le_of_unique' {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Unique κ] (Z : Matrix κ ι ℂ) : ((1 - Zᴴ * Z).det).re ≤ 1 := by
  rw [Matrix.det_one_sub_mul_comm]
  have := re_det_one_sub_le_of_unique (Zᴴ)
  rwa [Matrix.conjTranspose_conjTranspose] at this

end GlobalTheory.IntBall.DetLe

namespace GlobalTheory.IntBall

open GlobalTheory.IntBall.DetLe

theorem zDet_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 1 ∨ X.p0 + 1 = r) → ∀ z : V (nd X), z ∈ Om X → ∀ τ : X.Ψ, zDet X z τ ≤ 1 := by
  intro E _ _ _ r X h z _ τ
  have hle := X.p0_le
  unfold zDet
  rcases h with h | h
  · letI : Unique {b : Fin r // (b : ℕ) < X.p0} :=
      { default := ⟨⟨0, by omega⟩, by simp [h]⟩
        uniq := fun b => Subtype.ext (Fin.ext (by have := b.2; simp only; omega)) }
    exact re_det_one_sub_le_of_unique _
  · letI : Unique {a : Fin r // X.p0 ≤ (a : ℕ)} :=
      { default := ⟨⟨X.p0, by omega⟩, le_refl _⟩
        uniq := fun a => Subtype.ext (Fin.ext (by have := a.2; have := a.1.2; simp only; omega)) }
    exact re_det_one_sub_le_of_unique' _

end GlobalTheory.IntBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialRelationLocalRingBound
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differential_relation_local_ring_bound : ∀ (k K : Type) [Field k] [CharZero k] [Field K] [Algebra k K] (B : Subalgebra k K) (Q : Ideal B), Q.IsPrime → ∀ (s : B) (m : ℕ) (y : Fin m → K) (T : K) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ v : B, ∃ r : B, r ∉ Q ∧ ∃ c : Fin (m + 1) → B, (r : K) • D k K (v : K) = ∑ l, (c l : K) • (Fin.cons (D k K (s : K)) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) l) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * T = a * s ^ e) → ∃ N Dn : B, N ∉ Q ∧ Dn ∉ Q ∧ (Dn : K) • ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K T) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) = ((N : K) * (s : K) ^ (e - 1)) • ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) := by
  first | (exact @GlobalTheory.wedge_D_eq_pow_mul_wedge_D_of_eq_unit_mul_pow) | (exact GlobalTheory.wedge_D_eq_pow_mul_wedge_D_of_eq_unit_mul_pow) | (intros; apply GlobalTheory.wedge_D_eq_pow_mul_wedge_D_of_eq_unit_mul_pow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogBasisAndVanishingAboveDimensionStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dlog_basis_and_vanishing_above_dimension : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = (algebraMap F K (x j.succ / x 0))⁻¹ • D k K (algebraMap F K (x j.succ / x 0))) ∧ ∀ q, d < q → ∀ y ∈ ⋀[K]^q Ω[K⁄k], y = 0 := by
  first | (exact @GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish) | (exact GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish) | (intros; apply GlobalTheory.PD.IsFinCover.dlog_basis_and_vanish <;> assumption)
end

