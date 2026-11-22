import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ImaginaryRootConj
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrobAllEmbeddings
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

def frobKer {R C : Type} [CommRing R] [Field C] (V : VF C) (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : Ideal R where
  carrier := {x | V.MM (f x)}
  add_mem' := fun {a b} ha hb => by
    show 0 < V.v (f (a + b))
    rw [map_add]
    exact V.v.map_lt_add ha hb
  zero_mem' := by
    show 0 < V.v (f 0)
    rw [map_zero, V.v.map_zero]
    exact WithTop.coe_lt_top (0 : ℝ)
  smul_mem' := fun a b hb => by
    show 0 < V.v (f (a * b))
    rw [map_mul, V.v.map_mul]
    exact lt_of_lt_of_le hb (le_add_of_nonneg_left (hf a))

theorem frobKer_isPrime {R C : Type} [CommRing R] [Field C] (V : VF C) (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) :
    (frobKer V f hf).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]
    show ¬ 0 < V.v (f 1)
    rw [map_one, V.v.map_one]
    exact lt_irrefl _
  mem_or_mem' := fun {a b} h => by
    have h' : 0 < V.v (f (a * b)) := h
    rw [map_mul, V.v.map_mul] at h'
    by_contra hn
    push_neg at hn
    have h1 : V.v (f a) ≤ 0 := not_lt.1 hn.1
    have h2 : V.v (f b) ≤ 0 := not_lt.1 hn.2
    exact absurd (add_nonpos h1 h2) (not_le.2 h')

theorem exists_frob_of_hom {E C : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field C] (V : VF C)
    (f : 𝓞 E →+* C) (hf : ∀ x, V.Ge 0 (f x)) :
    ∃ φ : E ≃ₐ[ℚ] E, ∀ x : 𝓞 E, V.MM (f (φ • x) - f x ^ V.l) := by
  set P := frobKer V f hf with hP
  haveI : P.IsPrime := frobKer_isPrime V f hf
  have hl : ((V.l : ℕ) : 𝓞 E) ∈ P := by
    show 0 < V.v (f _)
    rw [map_natCast, V.v_l]
    exact zero_lt_one
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hl
    exact V.l_prime.ne_zero (by exact_mod_cast hl)
  haveI : Finite (𝓞 E ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  have hu : P.under ℤ = Ideal.span {(V.l : ℤ)} := by
    have hmax : (Ideal.span {(V.l : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast V.l_prime.ne_zero)).2
        (Nat.prime_iff_prime_int.1 V.l_prime)).isMaximal (by
          rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast V.l_prime.ne_zero)
    refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hl
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) P
  refine ⟨φ, fun x => ?_⟩
  have h := hφ x
  rw [hu, Int.card_ideal_quot] at h
  have h' : V.MM (f (φ • x - x ^ V.l)) := h
  rwa [map_sub, map_pow] at h'

theorem exists_aut_comp_eq {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (τ₀ τ : E →+* ℂ) :
    ∃ σ : E ≃ₐ[ℚ] E, τ = τ₀.comp (σ : E →+* E) := by
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) τ₀ τ (Subsingleton.elim _ _)
  exact ⟨σ.symm, hσ.symm⟩

theorem exists_frob_all_embeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → IsGalois ℚ E → (∀ σ σ' : E ≃ₐ[ℚ] E, σ * σ' = σ' * σ) → ∃ φ : E ≃ₐ[ℚ] E, ∀ (τ : E →+* ℂ) (x : 𝓞 E), V.MM (emA3 io ι (τ.comp (φ : E →+* E)) x - emA3 io ι τ x ^ V.l) := by
  intro E _ _ _ H lv c T io C _ _ V ι hι hG hab
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have key : ∀ (τ : E →+* ℂ) (s : E ≃ₐ[ℚ] E) (x : 𝓞 E),
      emA3 io ι (τ.comp (s : E →+* E)) x = emA3 io ι τ (s • x) := fun τ s x => rfl
  obtain ⟨φ, hφ⟩ := exists_frob_of_hom V (emA3 io ι τ₀)
    (fun x => GlobalTheory.RowChartCounterexample.em_int_holds τ₀ x hι)
  refine ⟨φ, fun τ x => ?_⟩
  obtain ⟨σ, rfl⟩ := exists_aut_comp_eq τ₀ τ
  rw [key, key, key, ← mul_smul, hab, mul_smul]
  exact hφ _

end GlobalTheory.RowAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMoveBack
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Jets

open TopologicalSpace in

theorem exists_gen_move_back : ∀ (Y Y' X₁ X₂ W : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂), L₁.IsLB → L₂.IsLB → ∀ (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → ∀ (K : Type) [Fintype K] (m : K → (Y' ⟶ Y)) (ε : K → ℤ) (φ₁ : K → (Y' ⟶ X₁)), (∀ k, φ₁ k = m k ≫ f₁) → ∀ (φ₂ : K → (W ⟶ X₂)) (h : Y' ⟶ W), (∀ k, h ≫ φ₂ k = m k ≫ f₂) → ∀ t : LB.Gen (LB.LinComb L₂ φ₂ ε), t.IsGen → ∃ a : LB.Gen (LB.LinComb L₁ φ₁ ε), a.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J₂ : (Z ⟶ X₂) → L₂.ι) (J₁ : (Z ⟶ X₁) → L₁.ι), Good L₂ z J₂ → Good L₁ z J₁ → val t (r ≫ h) z J₂ = (∏ k, isoVal w (r ≫ m k) z (J₂ ((r ≫ m k) ≫ f₂)) (J₁ ((r ≫ m k) ≫ f₁)) ^ ε k) * val a r z J₁ := by
  intro Y Y' X₁ X₂ W L₁ L₂ hL₁ hL₂ f₁ f₂ w hw K _ m ε φ₁ e₁ φ₂ h hc t ht
  classical
  obtain rfl : φ₁ = fun k => m k ≫ f₁ := funext e₁
  let O : (K → L₁.ι) → (K → L₂.ι) → Y'.Opens := fun q p =>
    LB.wchart L₁ (fun k => m k ≫ f₁) q ⊓ LB.wchart L₂ (fun k => m k ≫ f₂) p
  have pt : ∀ k y, φ₂ k (h y) = f₂ (m k y) := fun k y => congrArg (fun q : Y' ⟶ X₂ => q y) (hc k)
  have le1 : ∀ q p k, O q p ≤ m k ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => p k) ⊓ (L₁.pull f₁).U (fun _ => q k)) :=
    fun q p k y hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy.2 k), mem_pull.2 (Set.mem_iInter.1 hy.1 k)⟩
  have le2 : ∀ q p, O q p ≤ h ⁻¹ᵁ LB.wchart L₂ φ₂ p := fun q p y hy => Set.mem_iInter.2 fun k => by
    show φ₂ k (h y) ∈ L₂.U (p k)
    rw [pt]; exact Set.mem_iInter.1 hy.2 k
  let v : ∀ q p, Γ(Y', O q p)ˣ := fun q p =>
    (∏ k, res (le1 q p k) (pullU (m k) _ (w.s (fun _ => p k, fun _ => q k))) ^ ε k)⁻¹ *
      res (le2 q p) (pullU h _ (t.s p))
  have germ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (O q p) (v q p) =
        (∏ k, isoVal w (r ≫ m k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L₂ φ₂ p) (t.s p) := by
    intro Z r z q p hz
    have m2 := le2 q p hz
    show gm r z (O q p) ((∏ k, _)⁻¹ * _) = _
    rw [map_mul, map_inv, map_prod]
    refine congrArg₂ (· * ·) (congrArg (·⁻¹) (Finset.prod_congr rfl fun k _ => ?_))
      ((gm_res r z (le2 q p) hz _).trans (gm_pull r h z _ m2 _))
    have m1 := le1 q p k hz
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z (le1 q p k) hz _).trans
      (gm_pull r (m k) z _ m1 _)))
  have memO : ∀ q (y : Y'), y ∈ LB.wchart L₁ (fun k => m k ≫ f₁) q → ∃ p, y ∈ O q p := fun q y hy => by
    choose p hp using fun k => exists_chart hL₂ (f₂ (m k y))
    exact ⟨p, hy, Set.mem_iInter.2 fun k => hp k⟩
  have glue : ∀ q, ∃ s : Γ(Y', LB.wchart L₁ (fun k => m k ≫ f₁) q)ˣ,
      ∀ p, res (inf_le_left : O q p ≤ _) s = v q p := by
    intro q
    refine glue_unit _ (O q) (fun p => inf_le_left) (fun y hy => ?_) (v q) fun p p' y hy => ?_
    · obtain ⟨p, hp⟩ := memO q y hy
      exact Opens.mem_iSup.2 ⟨p, hp⟩
    · rw [germ _ _ y q p hy.1, germ _ _ y q p' hy.2]
      have hp : ∀ k, f₂ (m k y) ∈ L₂.U (p k) := fun k => Set.mem_iInter.1 hy.1.2 k
      have hp' : ∀ k, f₂ (m k y) ∈ L₂.U (p' k) := fun k => Set.mem_iInter.1 hy.2.2 k
      have hq : ∀ k, f₁ (m k y) ∈ L₁.U (q k) := fun k => Set.mem_iInter.1 hy.1.1 k
      have e1 : ∀ k, isoVal w (𝟙 Y' ≫ m k) y (p k) (q k) =
          gm (m k ≫ f₂) y _ (L₂.g (p k) (p' k)) * isoVal w (𝟙 Y' ≫ m k) y (p' k) (q k) := fun k => by
        rw [Category.id_comp, GlobalTheory.FieldBaseChange.isoVal_trans hw (m k) y (hp k) (hp' k) (hq k) (hq k),
          gm_self hL₁ (m k ≫ f₁) y (hq k), inv_one, _root_.mul_one]
      have e2 : trF φ₂ ε (𝟙 Y' ≫ h) y p p' = ∏ k, gm (m k ≫ f₂) y _ (L₂.g (p k) (p' k)) ^ ε k :=
        Finset.prod_congr rfl fun k _ => by rw [Category.id_comp, hc k]
      rw [gen_trans ht (𝟙 Y' ≫ h) y (le2 q p hy.1) (le2 q p' hy.2), e2]
      simp only [e1, mul_zpow, Finset.prod_mul_distrib, mul_inv_rev]
      rw [_root_.mul_assoc, inv_mul_cancel_left]
  choose s hs using glue
  have vals : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (LB.wchart L₁ (fun k => m k ≫ f₁) q) (s q) =
        (∏ k, isoVal w (r ≫ m k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L₂ φ₂ p) (t.s p) := by
    intro Z r z q p hz
    rw [← gm_res r z (inf_le_left : O q p ≤ _) hz, hs q p, germ Z r z q p hz]
  refine ⟨⟨s⟩, fun q q' => unit_ext fun y hy => ?_, fun Z r z J₂ J₁ hJ₂ hJ₁ => ?_⟩
  · have hq : ∀ k, f₁ (m k y) ∈ L₁.U (q k) := fun k => Set.mem_iInter.1 hy.1 k
    have hq' : ∀ k, f₁ (m k y) ∈ L₁.U (q' k) := fun k => Set.mem_iInter.1 hy.2 k
    choose p hp using fun k => exists_chart hL₂ (f₂ (m k y))
    have m0 : y ∈ O q p := ⟨hy.1, Set.mem_iInter.2 fun k => hp k⟩
    have m' : y ∈ O q' p := ⟨hy.2, Set.mem_iInter.2 fun k => hp k⟩
    rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy]
    show gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q) (s q) =
      gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q ⊓ LB.wchart L₁ (fun k => m k ≫ f₁) q')
      ((LB.LinComb L₁ (fun k => m k ≫ f₁) ε).g q q') * gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q') (s q')
    rw [gm_linComb L₁ (fun k => m k ≫ f₁) ε (𝟙 Y') y q q' hy.1 hy.2, vals _ _ y q p m0, vals _ _ y q' p m']
    have e3 : ∀ k, isoVal w (𝟙 Y' ≫ m k) y (p k) (q k) =
        (gm (𝟙 Y' ≫ m k ≫ f₁) y _ (L₁.g (q k) (q' k)))⁻¹ * isoVal w (𝟙 Y' ≫ m k) y (p k) (q' k) := fun k => by
      rw [Category.id_comp, Category.id_comp,
        GlobalTheory.FieldBaseChange.isoVal_trans hw (m k) y (hp k) (hp k) (hq k) (hq' k),
        gm_self hL₂ (m k ≫ f₂) y (hp k), _root_.one_mul]
    simp only [e3, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv_rev, inv_inv]
    exact (congrArg (· * _) (mul_comm _ _)).trans (_root_.mul_assoc _ _ _)
  · have m0 : r z ∈ O (fun k => J₁ ((r ≫ m k) ≫ f₁)) (fun k => J₂ ((r ≫ m k) ≫ f₂)) :=
      ⟨Set.mem_iInter.2 fun k => hJ₁ ((r ≫ m k) ≫ f₁), Set.mem_iInter.2 fun k => hJ₂ ((r ≫ m k) ≫ f₂)⟩
    rw [val_of t (r ≫ h) z J₂ (fun k => J₂ ((r ≫ m k) ≫ f₂))
        (fun k => by rw [Category.assoc, hc k, Category.assoc]),
      val_of _ r z J₁ (fun k => J₁ ((r ≫ m k) ≫ f₁)) (fun k => by rw [Category.assoc])]
    show _ = _ * gm r z (LB.wchart L₁ (fun k => m k ≫ f₁) _) (s _)
    rw [vals Z r z _ _ m0, mul_inv_cancel_left]

end GlobalTheory.Jets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHighestWeightIrreducibleUnitaryRepU
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.UnitaryHighestWeight

section OneParam

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem deriv_right (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (t : ℝ) :
    HasDerivAt (fun s => U s v) (U t (A v)) t := by
  have h1 : HasDerivAt (fun s => U (s - t) v) (A v) t := by
    have h := hd v
    rw [← sub_self t] at h
    exact HasDerivAt.comp_sub_const t t h
  have h2 := ((U t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  have h3 : HasDerivAt (fun s => U t (U (s - t) v)) (U t (A v)) t := h2
  convert h3 using 1
  funext s
  simp [← hadd]

theorem deriv_left (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (t : ℝ) :
    HasDerivAt (fun s => U s v) (A (U t v)) t := by
  have h1 : HasDerivAt (fun s => U (s - t) (U t v)) (A (U t v)) t := by
    have h := hd (U t v)
    rw [← sub_self t] at h
    exact HasDerivAt.comp_sub_const t t h
  convert h1 using 1
  funext s
  simp [← hadd]

theorem eigen (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (h0 : ∀ v, U 0 v = v)
    (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (v : W) (c : ℂ) (hv : A v = c • v) :
    U 1 v = Complex.exp c • v := by
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • U t v) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    have h2 := h1.fun_smul (deriv_right U A hadd hd v t)
    convert h2 using 1
    rw [hv, map_smul, smul_smul, ← add_smul]
    simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    one_smul, h0] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem stable [FiniteDimensional ℂ W] (U : ℝ → W →L[ℂ] W) (A : W →ₗ[ℂ] W) (h0 : ∀ v, U 0 v = v)
    (hadd : ∀ s t v, U (s + t) v = U s (U t v))
    (hd : ∀ v, HasDerivAt (fun t => U t v) (A v) 0) (S : Submodule ℂ W) (hS : ∀ v ∈ S, A v ∈ S)
    (v : W) (hv : v ∈ S) (t : ℝ) : U t v ∈ S := by
  set Q : W →L[ℂ] W := ContinuousLinearMap.id ℂ W - S.starProjection with hQ
  have hQ0 : ∀ y ∈ S, Q y = 0 := fun y hy => by
    simp [hQ, (Submodule.starProjection_eq_self_iff (K := S)).2 hy]
  set B : W →L[ℂ] W := Q.comp (LinearMap.toContinuousLinearMap A) with hB
  have hq : ∀ t, HasDerivAt (fun s => Q (U s v)) (B (Q (U t v))) t := by
    intro t
    have h2 : HasDerivAt (fun s => Q (U s v)) (Q (A (U t v))) t :=
      (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (deriv_left U A hadd hd v t)
    convert h2 using 1
    have h3 : Q (A (S.starProjection (U t v))) = 0 :=
      hQ0 _ (hS _ (Submodule.starProjection_apply_mem S _))
    have h4 : Q (U t v) = U t v - S.starProjection (U t v) := by simp [hQ]
    simp only [hB, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
    rw [h4, map_sub, map_sub, h3, sub_zero]
  have hz : (fun s => Q (U s v)) = fun _ => (0 : W) := by
    refine ODE_solution_unique_univ (v := fun _ y => B y) (s := fun _ => Set.univ) (K := ‖B‖₊) (t₀ := 0)
      (fun _ => B.lipschitz.lipschitzOnWith) (fun t => ⟨hq t, trivial⟩)
      (fun t => ⟨by simpa using hasDerivAt_const t (0 : W), trivial⟩) ?_
    simp only [h0]
    exact hQ0 v hv
  have h5 : U t v - S.starProjection (U t v) = 0 := by simpa [hQ] using congrFun hz t
  rw [sub_eq_zero.1 h5]
  exact Submodule.starProjection_apply_mem S _

end OneParam

open PI.UpqRep

theorem Jm_allPos (k : ℕ) : Jm (allPos k) = 1 := by
  simp [Jm, allPos]

theorem mem_K_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Jm (allPos k) = Jm (allPos k) * g) ↔
    gᴴ * Jm (allPos k) * g = Jm (allPos k)
  rw [Jm_allPos, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

theorem exp_mem {k : ℕ} {Z : Matrix (Fin k) (Fin k) ℂ} (hZ : Zᴴ = -Z) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Z) ∈ UJset (allPos k) := by
  refine Formalism.REAL.exp_indefinite_unitary_holds k (allPos k) Z ?_ t
  show Zᴴ * Jm (allPos k) + Jm (allPos k) * Z = 0
  rw [Jm_allPos, hZ]
  simp

variable {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)}

theorem group_zero (hπ : IsURepOn (UJset (allPos k)) π) (Z : Matrix (Fin k) (Fin k) ℂ) (v : W) :
    π (NormedSpace.exp (((0 : ℝ) : ℂ) • Z)) v = v := by
  simp [hπ.1.1]

theorem group_add (hπ : IsURepOn (UJset (allPos k)) π) {Z : Matrix (Fin k) (Fin k) ℂ} (hZ : Zᴴ = -Z)
    (s t : ℝ) (v : W) :
    π (NormedSpace.exp (((s + t : ℝ) : ℂ) • Z)) v =
      π (NormedSpace.exp ((s : ℂ) • Z)) (π (NormedSpace.exp ((t : ℂ) • Z)) v) := by
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute _ _
    (((Commute.refl Z).smul_left _).smul_right _), hπ.1.2 _ (exp_mem hZ s) _ (exp_mem hZ t)]
  rfl

theorem diag_skew (θ : Fin k → ℝ) :
    (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)ᴴ = -Matrix.diagonal fun a => (θ a : ℂ) * Complex.I := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  congr 1
  funext a
  simp

theorem exp_diag (θ : Fin k → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      Matrix.diagonal fun a => Complex.exp (((t * θ a : ℝ) : ℂ) * Complex.I) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext a
  rw [← Complex.exp_eq_exp_ℂ]
  simp [mul_assoc]

theorem sum_diag (E : Fin k → Fin k → Module.End ℂ W) (d : Fin k → ℂ) (v : W) :
    ∑ a, ∑ b, Matrix.diagonal d a b • E a b v = ∑ a, d a • E a a v := by
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.diagonal_apply, ite_smul]

theorem isWtOn_of_isWeight (hπ : IsURepOn (UJset (allPos k)) π) (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin k → ℝ) (v : W) (hv : Formalism.REAL.IsWeight E μ v) : IsWtOn (Kset (allPos k)) π μ v := by
  intro θ _
  have h := eigen (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)))
    (∑ a, ((θ a : ℂ) * Complex.I) • E a a) (group_zero hπ _) (group_add hπ (diag_skew θ))
    (fun w => by
      have := hE _ (diag_skew θ) w
      rw [sum_diag] at this
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using this)
    v (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) (by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hv _, smul_smul, ← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring)
  simp only [exp_diag, one_mul] at h
  exact h

theorem isWeight_of_isWtOn (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (μ : Fin k → ℝ) (v : W) (hv : IsWtOn (Kset (allPos k)) π μ v) : Formalism.REAL.IsWeight E μ v := by
  intro a
  set θ : Fin k → ℝ := Pi.single a 1 with hθ
  have h1 := hE _ (diag_skew θ) v
  rw [sum_diag] at h1
  have h2 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I)) v) =
      fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v := by
    funext t
    have hm := exp_mem (diag_skew θ) t
    rw [exp_diag] at hm ⊢
    rw [hv (fun b => t * θ b) ((mem_K_iff _).2 hm)]
    congr 2
    simp [hθ, Pi.single_apply]
    ring
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp ((μ a * Complex.I) * t) • v) ((μ a * Complex.I) • v) 0 := by
    have h4 : HasDerivAt (fun t : ℝ => (μ a * Complex.I) * (t : ℂ)) (μ a * Complex.I) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (μ a * Complex.I)
    simpa using h4.cexp.smul_const v
  rw [h2] at h1
  have h5 := h1.unique h3
  have h6 : ∑ b, ((θ b : ℂ) * Complex.I) • E b b v = Complex.I • E a a v := by
    rw [Finset.sum_eq_single a]
    · simp [hθ]
    · intro b _ hb
      simp [hθ, Pi.single_eq_of_ne hb]
    · simp
  rw [h6, mul_comm, ← smul_smul] at h5
  exact smul_right_injective W Complex.I_ne_zero h5

theorem stable_of_derived [FiniteDimensional ℂ W] (hπ : IsURepOn (UJset (allPos k)) π)
    (E : Fin k → Fin k → Module.End ℂ W)
    (hE : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
      HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0)
    (S : Submodule ℂ W) (hS : Formalism.REAL.KStable (allPos k) E S) :
    ∀ g ∈ UJset (allPos k), ∀ v ∈ S, π g v ∈ S := by
  intro g hg v hv
  obtain ⟨Y, hY, hg', -⟩ := Formalism.REAL.compact_exponential_surjective k (allPos k) g ((mem_K_iff g).2 hg)
  have hZ : Yᴴ = -Y := by
    have h : Yᴴ * Jm (allPos k) + Jm (allPos k) * Y = 0 := hY.1
    rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  have h := stable (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Y))) (∑ a, ∑ b, Y a b • E a b)
    (group_zero hπ _) (group_add hπ hZ)
    (fun w => by simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hE _ hZ w) S
    (fun w hw => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b rfl w hw)) v hv 1
  simpa [hg'] using h

theorem exists_isHCTypeU : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π → (∀ S : Submodule ℂ W, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∃ u, PI.UpqRep.IsHCTypeU k u π := by
  intro k W _ _ _ _ π hπ hirr
  obtain ⟨E, hgl, hun, hE⟩ := GlobalTheory.T.exists_derivedAction_finiteDimUnitaryRep k W π hπ
  obtain ⟨x, -, hx, Λ, hΛ⟩ := Formalism.REAL.highestWeightExists_holds W k (allPos k) E ⊤ inferInstance
    (Formalism.REAL.glRel_kRel _ E hgl) (Formalism.REAL.isUnitary_kUnit _ E hun) (fun _ _ _ _ _ => trivial) top_ne_bot
  have hxm : x ∈ Formalism.REAL.kSpan (allPos k) E x := Submodule.mem_sInf.2 fun S hS => hS.1
  have hst : Formalism.REAL.KStable (allPos k) E (Formalism.REAL.kSpan (allPos k) E x) := fun a b hab y hy =>
    Submodule.mem_sInf.2 fun S hS => hS.2 a b hab y (Submodule.mem_sInf.1 hy S hS)
  have htop : Formalism.REAL.kSpan (allPos k) E x = ⊤ := by
    rcases hirr _ (stable_of_derived hπ E hE _ hst) with h | h
    · rw [h] at hxm
      exact absurd hxm hx
    · exact h
  refine ⟨Λ - rhoN (allPos k) + rhoC (allPos k), inferInstance, inferInstance, hπ, ?_⟩
  have hl : lowK (allPos k) (Λ - rhoN (allPos k) + rhoC (allPos k)) = Λ := by
    unfold lowK
    abel
  rw [hl]
  refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ hS => hirr S fun g hg => hS g ((mem_K_iff g).2 hg),
    ⟨x, trivial, hx, isWtOn_of_isWeight hπ E hE Λ x hΛ.1⟩, fun μ v _ hv hw => ?_⟩
  exact GlobalTheory.T.weight_compactDominance_of_mem_highestWeightSpan k W E Λ μ x v hgl hun hΛ (htop ▸ trivial) hv (isWeight_of_isWtOn E hE μ v hw)

end GlobalTheory.UnitaryHighestWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLiftPointTranslationFieldPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_lift_translT_general {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (f : S' ⟶ S)
    (P : Over S') (x : P ⟶ (Over.pullback f).obj G) (T : Over S) (e : T.left ⟶ P.left) (r g : T ⟶ G)
    (hg : g.left = e ≫ x.left ≫ pullback.fst G.hom f) :
    ∃ ρ : T.left ⟶ (P ⊗ (Over.pullback f).obj G).left,
      ρ ≫ (fst P ((Over.pullback f).obj G)).left = e ∧
      ρ ≫ (snd P ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f = r.left ∧
      (ρ ≫ (translT ((Over.pullback f).obj G) x).left) ≫ (fst P ((Over.pullback f).obj G)).left = e ∧
      (ρ ≫ (translT ((Over.pullback f).obj G) x).left) ≫ (snd P ((Over.pullback f).obj G)).left ≫
        pullback.fst G.hom f = (r * g).left := by
  have hx : x.left ≫ pullback.snd G.hom f = P.hom := Over.w x
  have hT : T.hom = (e ≫ P.hom) ≫ f := by
    rw [← Over.w g, hg, ← hx]
    simp only [Category.assoc, pullback.condition]
  let T' : Over S' := Over.mk (e ≫ P.hom)
  let e' : T' ⟶ P := Over.homMk e rfl
  let r' : T' ⟶ (Over.pullback f).obj G :=
    Over.homMk (pullback.lift r.left (e ≫ P.hom) ((Over.w r).trans hT)) (pullback.lift_snd _ _ _)
  have hr' : r'.left ≫ pullback.fst G.hom f = r.left := pullback.lift_fst _ _ _
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk (𝟙 T.left) ((Category.id_comp _).trans hT)
  have hU : ∀ z : T ⟶ G, (U ≫ z).left = z.left := fun z => Category.id_comp _
  have h1 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ fst _ _ = e' := by
    simp [translT]
  have h2 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ snd _ _ = (e' ≫ x) * r' := by
    simp only [translT, translPt, lift_snd, Hom.mul_def]
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have h3 := (isGrpPullback_pullback G f).2 T' (e' ≫ x) r' (U ≫ g) (U ≫ r)
    ((hU g).trans (hg.trans (Category.assoc _ _ _).symm)) ((hU r).trans hr'.symm)
  refine ⟨(lift e' r').left, congrArg (fun z => z.left) (lift_fst e' r'), ?_, ?_, ?_⟩
  · exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z : T' ⟶ (Over.pullback f).obj G => z.left ≫ pullback.fst G.hom f) (lift_snd e' r'))).trans hr'
  · exact (Category.assoc _ _ _).trans (congrArg (fun z => z.left) h1)
  · have h4 : ((lift e' r').left ≫ (translT ((Over.pullback f).obj G) x).left) ≫
        (snd P ((Over.pullback f).obj G)).left = ((e' ≫ x) * r').left :=
      (Category.assoc _ _ _).trans (congrArg (fun z => z.left) h2)
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst G.hom f) h4)).trans (h3.symm.trans ?_)
    rw [← MonObj.comp_mul, hU, mul_comm]

theorem exists_lift_translT : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (T : Over (Spec (CommRingCat.of R))) (e : T.left ⟶ Spec (CommRingCat.of F)) (r g : T ⟶ G), g.left = e ≫ x.left ≫ pullback.fst G.hom (jK R) → ∃ ρ : T.left ⟶ (UnifPre.GF (G := G) F).left, ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ ρ ≫ UnifPre.gFK (G := G) F = r.left ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ UnifPre.gFK (G := G) F = (r * g).left := by
  intro R _ _ G _ _ F _ _ x T e r g hg
  exact exists_lift_translT_general G (jK R) (TFK (R := R) F) x T e r g hg

end GlobalTheory
end

