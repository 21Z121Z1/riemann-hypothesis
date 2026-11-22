import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLocalDerivationAlongFibreFieldOfAffi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.LocDerExtK
open GlobalTheory.LocDerExt

theorem rsT_eq {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    rsT s O = resG Y h s := dif_pos h

theorem exists_locDerK : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), IsAffineOpen W₀ → ∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDerK q p m D W₀ d ∧ d W₀ = d₀ := by
  intro K _ R _ Y X q p m D W₀ hW d₀ hadd hmul hbase
  have H : ∀ f : Γ(X, W₀), ∃ δ : Γ(X, X.basicOpen f) → Γ(Y, m ⁻¹ᵁ X.basicOpen f),
      (∀ a b, δ (a + b) = δ a + δ b) ∧
      (∀ a b, δ (a * b) = (m.app _).hom a * δ b + (m.app _).hom b * δ a) ∧
      ∀ a, δ (resG X (X.basicOpen_le f) a) = resG Y (pre_le m (X.basicOpen_le f)) (d₀ a) := by
    intro f
    haveI := hW.isLocalization_basicOpen f
    refine der_exists f (m.app (X.basicOpen f)).hom
      (fun a => resG Y (pre_le m (X.basicOpen_le f)) (d₀ a)) (fun a b => by simp only [hadd, map_add])
      (fun a b => ?_)
    have e : ∀ a, (m.app (X.basicOpen f)).hom (algebraMap Γ(X, W₀) Γ(X, X.basicOpen f) a) =
        resG Y (pre_le m (X.basicOpen_le f)) ((m.app W₀).hom a) :=
      fun a => app_res m (X.basicOpen_le f) a
    rw [e, e]
    simp only [hmul, map_add, map_mul]
  choose δ δadd δmul δres using H
  have compat : ∀ (f g : Γ(X, W₀)) (k : X.basicOpen g ≤ X.basicOpen f) (s : Γ(X, X.basicOpen f)),
      resG Y (pre_le m k) (δ f s) = δ g (resG X k s) := by
    intro f g k s
    haveI := hW.isLocalization_basicOpen f
    refine der_unique f ((m.app (X.basicOpen g)).hom.comp (resG X k))
      (fun s => resG Y (pre_le m k) (δ f s)) (fun s => δ g (resG X k s)) (fun a b => ?_)
      (fun a b => ?_) (fun a => ?_) s
    · simp only [δmul, map_add, map_mul, RingHom.comp_apply, app_res m k]
    · simp only [δmul, map_mul, RingHom.comp_apply]
    · change resG Y (pre_le m k) (δ f (resG X (X.basicOpen_le f) a)) =
        δ g (resG X k (resG X (X.basicOpen_le f) a))
      rw [res_res X, δres, δres, res_res Y]
  have G : ∀ (W : X.Opens), W ≤ W₀ → ∀ s : Γ(X, W), ∃ t : Γ(Y, m ⁻¹ᵁ W),
      ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG Y (pre_le m k) t = δ f (resG X k s) := by
    intro W h s
    obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing'
      (fun i : {f : Γ(X, W₀) // X.basicOpen f ≤ W} => m ⁻¹ᵁ X.basicOpen i.1)
      (m ⁻¹ᵁ W) (fun i => homOfLE (pre_le m i.2)) (cover m hW h)
      (fun i => δ i.1 (resG X i.2 s)) (fun i j => by
        have e : X.basicOpen (i.1 * j.1) = X.basicOpen i.1 ⊓ X.basicOpen j.1 := X.basicOpen_mul _ _
        have ki : X.basicOpen (i.1 * j.1) ≤ X.basicOpen i.1 := e.le.trans inf_le_left
        have kj : X.basicOpen (i.1 * j.1) ≤ X.basicOpen j.1 := e.le.trans inf_le_right
        have k : m ⁻¹ᵁ X.basicOpen i.1 ⊓ m ⁻¹ᵁ X.basicOpen j.1 ≤ m ⁻¹ᵁ X.basicOpen (i.1 * j.1) :=
          fun y hy => e.ge hy
        have e' : resG Y (pre_le m ki) (δ i.1 (resG X i.2 s)) =
            resG Y (pre_le m kj) (δ j.1 (resG X j.2 s)) := by
          rw [compat _ _ ki, compat _ _ kj, res_res X, res_res X]
        have e'' := congrArg (resG Y k) e'
        rw [res_res Y, res_res Y] at e''
        exact e'')
    exact ⟨t, fun f k => ht ⟨f, k⟩⟩
  choose t ht using G
  classical
  refine ⟨fun W s => if h : W ≤ W₀ then t W h s else 0, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_add, δadd]
  · intro W h a b
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [map_add, map_mul, map_mul, ht W h _ f k, ht W h _ f k, ht W h _ f k, map_mul, δmul, app_res m k, app_res m k]
  · intro W W' h' h a
    simp only [dif_pos h, dif_pos (h'.trans h)]
    refine sep m hW (h'.trans h) _ _ (fun f k => ?_)
    rw [rsT_eq (pre_le m h')]
    refine Eq.trans ?_ (res_res Y (pre_le m h') (pre_le m k) _).symm
    rw [ht W' _ _ f k, ht W h a f (k.trans h'), res_res X]
  · intro W h r
    simp only [dif_pos h]
    refine sep m hW h _ _ (fun f k => ?_)
    rw [ht W h _ f k, res_const, res_const, ← res_const p (X.basicOpen_le f), δres, hbase, res_const]
  · funext a
    simp only [dif_pos (le_refl W₀)]
    refine sep m hW le_rfl _ _ (fun f k => ?_)
    rw [ht W₀ _ _ f k, δres]

theorem locDerK_unique {K : Type} [Field K] {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp K}
    {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W₀ : X.Opens} (hW : IsAffineOpen W₀)
    (d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (h : LocDerK q p m D W₀ d)
    (h' : LocDerK q p m D W₀ d') (e : d W₀ = d' W₀) (W : X.Opens) (hle : W ≤ W₀) : d W = d' W := by
  funext s
  refine sep m hW hle _ _ (fun f k => ?_)
  rw [← rsT_eq (pre_le m k), ← rsT_eq (pre_le m k), ← h.res W _ k hle, ← h'.res W _ k hle]
  haveI := hW.isLocalization_basicOpen f
  refine der_unique f (m.app (X.basicOpen f)).hom (d _) (d' _) (h.mul _ (X.basicOpen_le f))
    (h'.mul _ (X.basicOpen_le f)) (fun a => ?_) _
  change d _ (resG X (X.basicOpen_le f) a) = d' _ (resG X (X.basicOpen_le f) a)
  rw [h.res W₀ _ _ le_rfl, h'.res W₀ _ _ le_rfl, e]

theorem exists_unique_locDerK : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), IsAffineOpen W₀ → (∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDerK q p m D W₀ d ∧ d W₀ = d₀) ∧ ∀ d d', LocDerK q p m D W₀ d → LocDerK q p m D W₀ d' → d W₀ = d' W₀ → ∀ W, W ≤ W₀ → d W = d' W :=
  fun K _ R _ Y X q p m D W₀ hW =>
    ⟨exists_locDerK K R Y X q p m D W₀ hW, fun d d' h h' e W hle => locDerK_unique hW d d' h h' e W hle⟩

end GlobalTheory.LocDerExtK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSumSingle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LieEigenbasis

theorem existsUnique_sum_single {k : Type} [Field k] {n N : ℕ} (s : Fin N → Fin n)
    (hs : Function.Injective s) (c : Fin n → k) (hc : ∀ i, i ∉ Set.range s → c i = 0) :
    ∃! d : Fin N → k, c = ∑ j, d j • (Pi.single (s j) 1 : Fin n → k) := by
  have h : ∀ (d : Fin N → k) (j : Fin N),
      (∑ j, d j • (Pi.single (s j) 1 : Fin n → k)) (s j) = d j := fun d j => by
    simp [Finset.sum_apply, Pi.single_apply, hs.eq_iff]
  refine ⟨fun j => c (s j), funext fun i => ?_, fun d hd => funext fun j => by rw [hd, h]⟩
  by_cases hi : i ∈ Set.range s
  · obtain ⟨j, rfl⟩ := hi
    rw [h]
  · rw [hc i hi, Finset.sum_apply]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have : i ≠ s j := fun e => hi ⟨j, e.symm⟩
    simp [this]

end GlobalTheory.LieEigenbasis

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap) in

theorem GlobalTheory.lieMult_of_eigenbasis : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (G : Over (Sp k)) [GrpObj G] (act : OAct O G) (n : ℕ) (v : Fin n → (epsR k ⟶ G)) (τs : Fin n → (O →+* k)), Smooth G.hom → IsLieBasis v → (∀ i a, (v i ≫ act.act a).left = spMap (epsScale (τs i a)) ≫ (v i).left) → ∀ τ : O →+* k, LieMult act (𝟙 (Sp k)) τ (Nat.card {i // τs i = τ}) := by
  intro k _ O _ G _ act n v τs _ hv hτ τ
  have := act.hom
  obtain ⟨x, hx, hxv⟩ := Chart.chart_of_basis hv
  have hxv' : ∀ j, v j = tvec (x := x) (Pi.single j 1) := hxv
  have hdiag : ∀ a i, tmap hx (act.act a) (Pi.single i 1) = τs i a • (Pi.single i 1 : Fin n → k) :=
    fun a i => (Chart.tvec_eig_iff hx _ _ _).1 (by
      rw [← hxv']; exact Over.OverMorphism.ext (hτ i a))
  have hmap : ∀ a c i, tmap hx (act.act a) c i = τs i a * c i := fun a c i => by
    conv_lhs => rw [← Finset.univ_sum_single c]
    have : ∀ j, (Pi.single j (c j) : Fin n → k) = c j • (Pi.single j 1 : Fin n → k) := fun j => by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    simp only [this, map_sum, map_smul, hdiag]
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  let N := Nat.card {i // τs i = τ}
  let q : Fin N ≃ {i // τs i = τ} := (Finite.equivFin _).symm
  let s : Fin N → Fin n := fun j => (q j).1
  have hs : Function.Injective s := Subtype.val_injective.comp q.injective
  have hpr : ∀ d : Fin N → k, prodPts d (fun j => v (s j)) =
      tvec (x := x) (∑ j, d j • (Pi.single (s j) 1 : Fin n → k)) := fun d => by
    have ht : ∀ j, Chart.IsTan (v (s j)) := fun j => (Chart.isTan_iff _).2 (hv.1 _)
    obtain ⟨h, e⟩ := Chart.prodPts_tan hx d (fun j => v (s j)) ht
    refine (Chart.tcoord_spec hx _ h).trans ?_
    change tvec (x := x) _ = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Chart.tcoord_eq hx _ (ht j) _ (hxv _)]
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ G) ≃* (epsR k ⟶ G) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl G)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ G).left = η[G].left := Category.id_comp _
  refine LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ)
    (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (P := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w)
    (fun w => and_congr (by rw [IsTangent, he', one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he']
      rfl))
    (fun c u v => by rw [he', he']; rfl) N ⟨fun j => v (s j), fun j => ⟨hv.1 _, fun a => ?_⟩, ?_⟩
  · have := hτ (s j) a
    rw [(q j).2] at this
    exact Over.OverMorphism.ext this
  · rintro w ⟨hw, hw'⟩
    have ht := (Chart.isTan_iff _).2 hw
    obtain ⟨c, rfl⟩ : ∃ c, w = tvec (x := x) c := ⟨_, Chart.tcoord_spec hx w ht⟩
    refine (existsUnique_congr fun d => ?_).1
      (LieEigenbasis.existsUnique_sum_single s hs c fun i hi => ?_)
    · refine Iff.trans ?_ (Chart.isLieComb_iff d _ _).symm
      rw [hpr]
      exact ⟨fun h => by rw [← h], Chart.tvec_inj hx⟩
    · by_contra hc
      refine hi ⟨q.symm ⟨i, RingHom.ext fun a => ?_⟩, by simp [s]⟩
      have := congrFun ((Chart.tvec_eig_iff hx _ _ _).1 (hw' a)) i
      rw [hmap] at this
      exact mul_right_cancel₀ hc this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankEigenspaceOfLieMultiplicity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.UnifEigenRank

theorem finrank_of_existsUnique {k V : Type} [Field k] [AddCommGroup V] [Module k V] (E : Submodule k V) {n : ℕ}
    (W : Fin n → V) (hW : ∀ i, W i ∈ E) (h : ∀ z ∈ E, ∃! c : Fin n → k, z = ∑ i, c i • W i) :
    Module.finrank k E = n := by
  let W' : Fin n → E := fun i => ⟨W i, hW i⟩
  have hc : ∀ c : Fin n → k, ((Fintype.linearCombination k W' c : E) : V) = ∑ i, c i • W i := fun c => by
    simp [Fintype.linearCombination_apply, W']
  have hb : Function.Bijective (Fintype.linearCombination k W') := by
    refine (Function.bijective_iff_existsUnique _).2 fun z => ?_
    refine (existsUnique_congr fun c => ?_).1 (h z z.2)
    rw [Subtype.ext_iff, hc, eq_comm]
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_fin_fun]

end GlobalTheory.UnifEigenRank

open GlobalTheory.UnifLieBasis in
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD isTan_iff isLieComb_iff isTan_scale) in

theorem GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : Type) [CommRing O] (act : OAct O P₀.A) (F : O → Module.End ℂ (Fin P₀.g → ℂ)), (∀ a z, u.ex (F a z) = u.ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ), LieMult act (𝟙 _) τ n → Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = n := by
  intro P₀ u Hm χ hu O _ act F hF τ n hn
  have := act.hom
  let j : epsPt (𝟙 (Sp ℂ)) ≅ epsR ℂ := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp ℂ)) ⟶ P₀.A) ≃* (epsR ℂ ⟶ P₀.A) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl P₀.A)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have one : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ P₀.A).left = η[P₀.A].left := Category.id_comp _
  obtain ⟨v, hv, hb⟩ := LiePull.basis_transport e (P := IsLieEigen act (𝟙 _) τ)
    (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R' := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (Q := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w)
    (fun w => and_congr (by rw [IsTangent, he, one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he]
      rfl))
    (fun c u v => by rw [he, he]; rfl) n hn
  have key : ∀ (z : Fin P₀.g → ℂ) (w : epsR ℂ ⟶ P₀.A), IsTangent w → u.IsDiff z w →
      ((∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w) ↔
        z ∈ ⨅ a, Module.End.eigenspace (F a) (τ a)) := by
    intro z w hw hd
    rw [Submodule.mem_iInf]
    refine forall_congr' fun a => ?_
    rw [Module.End.mem_eigenspace_iff]
    have h1 : u.IsDiff (F a z) (w ≫ act.act a) :=
      isDiff_comp u (act.act a) (LinearMap.toContinuousLinearMap (F a)) (hF a) hw hd
    have h2 := isDiff_smul u ((isTan_iff _).2 hw) hd (τ a)
    have t1 := isTangent_comp (act.act a) hw
    have t2 := (isTan_iff _).1 (isTan_scale (τ a) ((isTan_iff _).2 hw))
    constructor
    · intro h
      exact (hu.tan₁ _ t1).unique h1 (by rw [h]; exact h2)
    · intro h
      rw [h] at h1
      exact (hu.tan₂ _).unique ⟨t1, h1⟩ ⟨t2, h2⟩
  choose W hW using fun i => (hu.tan₁ (v i) (hv i).1).exists
  have ht : ∀ i, Chart.IsTan (R := ℂ) (G := P₀.A) (v i) := fun i => (isTan_iff _).2 (hv i).1
  have hp : ∀ c : Fin n → ℂ, IsTangent (prodPts (R := ℂ) (G := P₀.A) c v) ∧
      u.IsDiff (∑ i, c i • W i) (prodPts (R := ℂ) (G := P₀.A) c v) := by
    intro c
    obtain ⟨a, b⟩ := isDiff_list_prod u (fun i => c i • W i) _
      (fun i => isTan_scale (c i) (ht i)) (fun i => isDiff_smul u (ht i) (hW i) (c i))
    exact ⟨(isTan_iff _).1 a, b⟩
  refine UnifEigenRank.finrank_of_existsUnique _ W (fun i => (key _ _ (hv i).1 (hW i)).1 (hv i).2) fun z hz => ?_
  obtain ⟨w, hw, hd⟩ := (hu.tan₂ z).exists
  refine (existsUnique_congr fun c => ?_).1 (hb w ⟨hw, (key _ _ hw hd).2 hz⟩)
  refine Iff.trans (isLieComb_iff c v w) ⟨fun h => ?_, fun h => ?_⟩
  · exact (hu.tan₁ _ hw).unique hd (by rw [h]; exact (hp c).2)
  · rw [h] at hd
    exact (hu.tan₂ _).unique ⟨hw, hd⟩ (hp c)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationUniformisedAbelianVarietyUniqueVec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.KS.TangentAt

def dval {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    DualNumber ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE U ⊤ h).hom f)

theorem dval_comp {X Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (t : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (v ≫ t) ⁻¹ᵁ U) (V : X.Opens) (e : V ≤ t ⁻¹ᵁ U) (hV : ⊤ ≤ v ⁻¹ᵁ V) (f : Γ(Y, U)) :
    dval (v ≫ t) U h f = dval v V hV ((t.appLE U V e).hom f) := by
  simp only [dval, ← Scheme.Hom.appLE_comp_appLE v t U V ⊤ e hV, CommRingCat.hom_comp, RingHom.comp_apply]

private theorem ΓSpecIso_appLE_spMap_top {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e : (⊤ : (Sp S).Opens) ≤ spMap φ ⁻¹ᵁ ⊤)
    (a : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((Scheme.Hom.appLE (spMap φ) ⊤ ⊤ e).hom a) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
  have key := congrArg (fun k => k.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  rw [← key]
  rfl

theorem fst_dval {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    (dval v U h f).fst = valAt' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) U f := by
  have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := fun x _ =>
    h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x))
  rw [valAt', dif_pos h', valAt, dval, ← Scheme.Hom.appLE_comp_appLE _ v U ⊤ ⊤ h (fun _ _ => trivial),
    CommRingCat.hom_comp, RingHom.comp_apply]
  exact (ΓSpecIso_appLE_spMap_top (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom _ _).symm

private theorem mem_prime_dualNumber_iff_fst_eq_zero (p : Ideal (DualNumber ℂ)) (hp : p.IsPrime) (x : DualNumber ℂ) :
    x ∈ p ↔ x.fst = 0 := by
  constructor
  · intro hx
    by_contra hne
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx
      (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne)))
  · intro h0
    have hsq : x * x = 0 := by
      ext <;> simp [h0]
    exact hp.mem_of_pow_mem 2 (by rw [pow_two, hsq]; exact p.zero_mem)

theorem top_le_iff_dual {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ U ↔ ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := by
  constructor
  · intro hv x _
    exact hv (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x))
  · intro hv y _
    let x : ↥(Sp ℂ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have e : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x = y := by
      apply PrimeSpectrum.ext
      ext a
      exact (mem_prime_dualNumber_iff_fst_eq_zero _ (PrimeSpectrum.isPrime _) a).trans
        (mem_prime_dualNumber_iff_fst_eq_zero _ (show PrimeSpectrum (DualNumber ℂ) from y).isPrime a).symm
    have hx : v.base ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x) ∈ U := hv (Set.mem_univ x)
    rw [e] at hx
    exact hx

private theorem top_le_preimage_top' {X Y : Scheme.{0}} (f : X ⟶ Y) : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

theorem comp_eq_spMap {X : Scheme.{0}} (p : X ⟶ Sp ℂ) (v : Sp (DualNumber ℂ) ⟶ X)
    (h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ p = 𝟙 _)
    (h2 : ∀ a, (dval v ⊤ le_top (constFn p ⊤ a)).snd = 0) :
    v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) := by
  have hD : ∀ c : ℂ, dval (v ≫ p) ⊤ (top_le_preimage_top' _) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c) =
      algebraMap ℂ (DualNumber ℂ) c := by
    intro c
    apply TrivSqZeroExt.ext
    · rw [fst_dval, h1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
        show (𝟙 (Sp ℂ)) = spMap (RingHom.id ℂ) by simp [spMap],
        valAt', dif_pos (top_le_preimage_top' _), valAt]
      exact (ΓSpecIso_appLE_spMap_top (RingHom.id ℂ) _ _).trans (by simp)
    · rw [dval_comp v p ⊤ (top_le_preimage_top' _) ⊤ (top_le_preimage_top' _) (top_le_preimage_top' _)]
      refine (h2 c).trans ?_
      rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv,
    ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom]
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  refine (hD c).trans ?_
  have k := ΓSpecIso_appLE_spMap_top (algebraMap ℂ (DualNumber ℂ)) (top_le_preimage_top' _)
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)
  rw [Iso.inv_hom_id_apply] at k
  exact k.symm

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)

def tr (a : Fin g → ℂ) : A ⟶ A := (toUnit A ≫ u.ex a) * 𝟙 A

theorem comp_tr {B : Over (Sp ℂ)} (x : B ⟶ A) (a : Fin g → ℂ) : x ≫ tr u a = (toUnit B ≫ u.ex a) * x := by
  rw [tr, comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit B), Category.comp_id]

theorem ex_tr (a z : Fin g → ℂ) : u.ex z ≫ tr u a = u.ex (a + z) := by
  rw [comp_tr, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, u.ex_add]

theorem ex_zero : u.ex 0 = 1 := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  exact _root_.mul_eq_left.mp h.symm

theorem tr_neg_tr (a : Fin g → ℂ) : tr u (-a) ≫ tr u a = 𝟙 A := by
  rw [comp_tr, tr, ← _root_.mul_assoc, ← comp_mul, ← u.ex_add, add_neg_cancel, ex_zero, comp_one, _root_.one_mul]

def DiffAt (v : Sp (DualNumber ℂ) ⟶ A.left) (z w : Fin g → ℂ) : Prop :=
  ∀ (U : A.left.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(A.left, U)),
    (dval v U h f).snd = fderiv ℂ (fun z' => valAt' (u.ex z').left U f) z w

theorem DiffAt.tr {v : Sp (DualNumber ℂ) ⟶ A.left} {z w : Fin g → ℂ} (h : DiffAt u v z w) (a : Fin g → ℂ) :
    DiffAt u (v ≫ (tr u a).left) (a + z) w := by
  have nat : ∀ {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
      (e : V ≤ φ ⁻¹ᵁ U) (hx : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, U)),
      valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f := by
    intro X Y x φ U V e hx f
    have hxφ : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := fun y hy => e (hx hy)
    rw [valAt', dif_pos hx, valAt', dif_pos hxφ, valAt, valAt, ← Scheme.Hom.appLE_comp_appLE x φ U V ⊤ e hx,
      CommRingCat.hom_comp, RingHom.comp_apply]
  intro U h' f
  have hV : ⊤ ≤ v ⁻¹ᵁ ((TangentAt.tr u a).left ⁻¹ᵁ U) := h'
  rw [dval_comp v (TangentAt.tr u a).left U h' _ le_rfl hV f, h]
  have hfun : (fun z' => valAt' (u.ex z').left ((TangentAt.tr u a).left ⁻¹ᵁ U) (((TangentAt.tr u a).left.appLE U _ le_rfl).hom f)) =
      fun z' => valAt' (u.ex (a + z')).left U f := by
    funext z'
    by_cases hz : ⊤ ≤ (u.ex z').left ⁻¹ᵁ ((TangentAt.tr u a).left ⁻¹ᵁ U)
    · rw [nat _ _ _ _ _ hz, ← Over.comp_left, ex_tr]
    · have hz' : ¬ ⊤ ≤ (u.ex (a + z')).left ⁻¹ᵁ U := by
        rw [← ex_tr, Over.comp_left]
        exact hz
      rw [valAt', dif_neg hz, valAt', dif_neg hz']
  rw [hfun]
  exact congrArg (fun L => L w) (fderiv_comp_add_left (𝕜 := ℂ) (f := fun y => valAt' (u.ex y).left U f) a)

theorem diffAt_iff (v : Sp (DualNumber ℂ) ⟶ A.left) (z w : Fin g → ℂ) :
    DiffAt u v z w ↔ DiffAt u (v ≫ (tr u (-z)).left) 0 w := by
  constructor
  · intro h
    have h' := DiffAt.tr u h (-z)
    rwa [neg_add_cancel] at h'
  · intro h
    have h' := DiffAt.tr u h z
    rwa [add_zero, Category.assoc, ← Over.comp_left, tr_neg_tr, Over.id_left, Category.comp_id] at h'

theorem existsUnique_vector (htan : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (z : Fin g → ℂ)
    (δ : ∀ W : A.left.Opens, Γ(A.left, W) → ℂ) (hδ : PtDer (u.ex z).left δ)
    (hc : ∀ a, δ ⊤ (constFn A.hom ⊤ a) = 0) :
    ∃! w, ∀ O f, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → δ O f = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  obtain ⟨v, ⟨hv0, hvd⟩, -⟩ := PtDual.existsUnique_point hδ
  have hv0' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = (u.ex z).left := hv0
  have hvd' : ∀ (W : A.left.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(A.left, W)), (dval v W h f).snd = δ W f := hvd
  have hone : (u.ex 0).left = (η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left := by
    rw [ex_zero]
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ (tr u (-z)).left =
      (η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left := by
    rw [← Category.assoc, hv0', ← Over.comp_left, ex_tr, neg_add_cancel, hone]
  have h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v ≫ (tr u (-z)).left) ≫ A.hom = 𝟙 _ := by
    rw [← Category.assoc, h0]
    exact Over.w _
  have hc' : ∀ a, (dval (v ≫ (tr u (-z)).left) ⊤ (top_le_preimage_top' _) (constFn A.hom ⊤ a)).snd = 0 := by
    intro a
    rw [dval_comp v (tr u (-z)).left ⊤ _ ⊤ (top_le_preimage_top' _) (top_le_preimage_top' _), hvd']
    have e3 := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE (tr u (-z)).left A.hom ⊤ ⊤ ⊤ (top_le_preimage_top' _)
        (top_le_preimage_top' _))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e3
    have key : ∀ (k : A.left ⟶ Sp ℂ) (_ : k = A.hom) (e : ⊤ ≤ k ⁻¹ᵁ ⊤),
        (k.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = constFn A.hom ⊤ a := by
      rintro _ rfl e
      rfl
    have e4 : ((tr u (-z)).left.appLE ⊤ ⊤ (top_le_preimage_top' _)).hom (constFn A.hom ⊤ a) =
        constFn A.hom ⊤ a := e3.trans (key _ (Over.w _) _)
    rw [e4]
    exact hc a
  let v'' : epsR ℂ ⟶ A := Over.homMk (v ≫ (tr u (-z)).left) (comp_eq_spMap A.hom _ h1 hc')
  have htv : IsTangent v'' := h0
  obtain ⟨w, hw, huniq⟩ := htan v'' htv
  have hdiff : ∀ w', u.IsDiff w' v'' ↔ DiffAt u (v ≫ (tr u (-z)).left) 0 w' := fun _ => Iff.rfl
  refine ⟨w, ?_, ?_⟩
  · intro O f hO
    have hv : ⊤ ≤ v ⁻¹ᵁ O := (top_le_iff_dual v O).2 (by rw [hv0']; exact hO)
    rw [← hvd' O hv f]
    exact ((diffAt_iff u v z w).2 ((hdiff w).1 hw)) O hv f
  · intro w' hw'
    apply huniq
    rw [hdiff, ← diffAt_iff]
    intro U h f
    rw [hvd' U h f]
    exact hw' U f (by rw [← hv0']; exact (top_le_iff_dual v U).1 h)

theorem tangent_at_point : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ z δ, PtDer (u.ex z).left δ → (∀ a, δ ⊤ (constFn P₀.A.hom ⊤ a) = 0) → ∃! w, ∀ O f, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → δ O f = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  intro P₀ u Hm χ hG z δ hδ hc
  obtain ⟨-, htan, -, -, -⟩ := hG
  exact existsUnique_vector u htan z δ hδ hc

end GlobalTheory.KS.TangentAt

end
end

