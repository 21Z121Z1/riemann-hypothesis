import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AevalEqZeroOfMemSatIdealModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver mIdealOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

noncomputable section

section Objects

variable (S : Type) [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [Algebra S Ω]

def dehom (y : (Σ k, ι k) → Ω) (J : Ideal (MRingOver S ι)) (d : ∀ k, ι k) : Set Ω :=
  {u | ∃ (g : MRingOver S ι) (a : K → ℕ), g ∈ J ∧ IsMultiHomog g a ∧
    u = aeval y g * ∏ k, y ⟨k, d k⟩ ^ (-(a k : ℤ))}

def satIdeal (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Ideal (MRingOver S ι)) :
    Ideal (Kleiman.Poly S N) :=
  Ideal.span {f | ∃ n : ℕ, f.IsHomogeneous n ∧ ∀ i, baseVec y k₀ e i ≠ 0 → ∀ d : ∀ k, ι k,
    (∀ k, y ⟨k, d k⟩ ≠ 0) → aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) f ∈
      Submodule.span (overRing (S := S) y k₀ e d i) (dehom S y J d)}

end Objects

section Facts

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
  {J : Ideal (MRingOver S ι)}

theorem mem_dehom {g : MRingOver S ι} {a : K → ℕ} (hg : g ∈ J) (ha : IsMultiHomog g a) (d : ∀ k, ι k) :
    aeval y g * ∏ k, y ⟨k, d k⟩ ^ (-(a k : ℤ)) ∈ dehom S y J d :=
  ⟨g, a, hg, ha, rfl⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_ratio_mem_chartRing (i : Fin (N + 1)) (p : Kleiman.Poly S N) :
    aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) p ∈
      ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.chartRing
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨p, rfl⟩

theorem aeval_mem_of_mem_satIdeal [DecidableEq K] {p : Kleiman.Poly S N} (hp : p ∈ satIdeal S y k₀ e J) {i : Fin (N + 1)}
    (hi : baseVec y k₀ e i ≠ 0) {d : ∀ k, ι k} (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) :
    aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) p ∈
      Submodule.span (overRing (S := S) y k₀ e d i) (dehom S y J d) := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n, -, hf⟩ := hf
    exact hf i hi d hd
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha =>
    rw [smul_eq_mul, map_mul]
    have hr : aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) r ∈ overRing (S := S) y k₀ e d i :=
      chartRing_le_overRing d i (aeval_ratio_mem_chartRing i r)
    have := Submodule.smul_mem _ (⟨_, hr⟩ : overRing (S := S) y k₀ e d i) ha
    rwa [Subalgebra.smul_def] at this

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem satIdeal_isHomogeneous :
    (satIdeal S y k₀ e J).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) S) :=
  Ideal.homogeneous_span _ _ fun _ ⟨n, hf, _⟩ => ⟨n, (mem_homogeneousSubmodule n _).2 hf⟩

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem homogeneousComponent_mem_satIdeal {p : Kleiman.Poly S N} (hp : p ∈ satIdeal S y k₀ e J) (n : ℕ) :
    homogeneousComponent n p ∈ satIdeal S y k₀ e J :=
  homogeneousComponent_mem_of_mem satIdeal_isHomogeneous hp n

theorem one_mem_dehom_top (d : ∀ k, ι k) : (1 : Ω) ∈ dehom S y (⊤ : Ideal (MRingOver S ι)) d := by
  classical
  refine ⟨1, 0, Submodule.mem_top, ?_, ?_⟩
  · intro m hm k
    have : m = 0 := by
      by_contra h
      exact (mem_support_iff.mp hm) (by rw [coeff_one, if_neg (Ne.symm h)])
    simp [this]
  · simp

theorem one_mem_satIdeal_top : (1 : Kleiman.Poly S N) ∈ satIdeal S y k₀ e (⊤ : Ideal (MRingOver S ι)) := by
  classical
  refine Ideal.subset_span ⟨0, isHomogeneous_one _ _, fun i _ d _ => ?_⟩
  rw [map_one]
  exact Submodule.subset_span (one_mem_dehom_top d)

theorem mem_satIdeal_of_aeval_eq_zero {f : Kleiman.Poly S N} {n : ℕ} (hf : f.IsHomogeneous n)
    (h0 : aeval (baseVec y k₀ e) f = 0) : f ∈ satIdeal S y k₀ e J :=
  Ideal.subset_span ⟨n, hf, fun i _ d _ => by
    rw [Kleiman.aeval_div_of_isHomogeneous (x := baseVec y k₀ e) hf i, h0, zero_div]
    exact zero_mem _⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_eq_zero_of_mem_mIdealOver {g : MRingOver S ι} (hg : g ∈ mIdealOver S y) : aeval y g = 0 := by
  have h : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.mConeMapOver S y g = 0 := hg
  have h1 := congrArg (MvPolynomial.eval (fun _ : K => (1 : Ω))) h
  rw [map_zero, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.mConeMapOver, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left] at h1
  rw [MvPolynomial.aeval_def]
  convert h1 using 2
  · ext r
    rw [RingHom.comp_apply, MvPolynomial.algebraMap_apply, MvPolynomial.eval_C]
  · funext p
    simp

theorem eq_zero_of_mem_dehom_mIdealOver {d : ∀ k, ι k} {u : Ω} (hu : u ∈ dehom S y (mIdealOver S y) d) :
    u = 0 := by
  obtain ⟨g, a, hg, -, rfl⟩ := hu
  rw [aeval_eq_zero_of_mem_mIdealOver hg, zero_mul]

theorem aeval_eq_zero_of_mem_satIdeal_model [DecidableEq K] {f : Kleiman.Poly S N} {n : ℕ}
    (hf : f.IsHomogeneous n) (hmem : f ∈ satIdeal S y k₀ e (mIdealOver S y)) {d : ∀ k, ι k}
    (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) : aeval (baseVec y k₀ e) f = 0 := by
  have hi : baseVec y k₀ e (e (d k₀)) ≠ 0 := by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hd k₀
  have h1 := aeval_mem_of_mem_satIdeal hmem hi hd
  have h2 : Submodule.span (overRing (S := S) y k₀ e d (e (d k₀))) (dehom S y (mIdealOver S y) d) = ⊥ := by
    rw [Submodule.span_eq_bot]
    intro u hu
    exact eq_zero_of_mem_dehom_mIdealOver hu
  rw [h2, Submodule.mem_bot, Kleiman.aeval_div_of_isHomogeneous (x := baseVec y k₀ e) hf] at h1
  exact (div_eq_zero_iff.1 h1).resolve_right (pow_ne_zero _ hi)

end Facts

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AltSumEqOfEventually
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

noncomputable section

section Poly

variable {K : Type}

theorem eval_bind₁_shift (p : MvPolynomial K ℚ) (a z : K → ℚ) :
    eval z (bind₁ (fun k => X k - C (a k)) p) = eval (z - a) p := by
  show eval₂Hom (RingHom.id ℚ) z _ = _
  rw [eval₂Hom_bind₁]
  have hfun : (fun i => eval₂Hom (RingHom.id ℚ) z (X i - C (a i))) = z - a := funext fun k => by simp
  rw [hfun]
  rfl

theorem altSum_eq_of_eventually (p : MvPolynomial K ℚ) {n : ℕ} (δ : Fin n → K → ℤ) (D : ℚ)
    (h : ∀ᶠ m : K → ℤ in atTop,
      ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D)
    (z : K → ℤ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((z - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D := by
  classical
  let q : MvPolynomial K ℚ := ∑ T : Finset (Fin n),
    C ((-1 : ℚ) ^ T.card) * bind₁ (fun k => X k - C (((∑ i ∈ T, δ i) k : ℤ) : ℚ)) p
  have hq : ∀ w : K → ℤ, eval (fun k => (w k : ℚ)) q =
      ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((w - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p := by
    intro w
    simp only [q, map_sum, map_mul, eval_C, eval_bind₁_shift]
    refine Finset.sum_congr rfl fun T _ => ?_
    congr 3
    funext k
    simp
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp h
  let s : K → Set ℚ := fun k => (fun t : ℤ => (t : ℚ)) '' Set.Ici (m₀ k)
  have hs : ∀ k, (s k).Infinite := fun k =>
    (Set.Ici_infinite (m₀ k)).image (fun a _ b _ hab => Int.cast_injective hab)
  have hqD : q = C D := by
    refine funext_set s hs fun w hw => ?_
    have hw' : ∀ k, ∃ t : ℤ, m₀ k ≤ t ∧ (t : ℚ) = w k := fun k => hw k (Set.mem_univ k)
    choose m hm1 hm2 using hw'
    have hwm : w = fun k => (m k : ℚ) := funext fun k => (hm2 k).symm
    rw [hwm, hq, eval_C]
    exact hm₀ m hm1
  rw [← hq, hqD, eval_C]

end Poly

theorem NumModel.proof (hT : TensorRealise.Statement) (hS : SectionsPoly.Statement) (hD : ModelDim.Statement) :
    NumModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n L δ hL hsub
  classical
  obtain ⟨i₀, hi₀⟩ := hmod.1 k₀
  have hj : x (e i₀) ≠ 0 := by
    rw [hx]
    simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi₀
  have hP := isMultiProjPrime_mIdealOver (S := F) y hmod.1
  have hdim := (hD F K ι Ω y k₀ N e x hx hmod n).mp hsub
  obtain ⟨p, hpH, hpS⟩ := hS F K ι Ω y k₀ hmod
  have hMD := (FieldNumbers.MixedDiffConst.full F K ι (mIdealOver F y) hP.multiHomog hP.relevant n hdim).1 δ
  set D := NumbersDVR.intNum F (mIdealOver F y) δ with hD_def

  have hev : ∀ᶠ m : K → ℤ in atTop, ∑ T : Finset (Fin n),
      (-1 : ℚ) ^ T.card * eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D := by
    have h2 : ∀ T : Finset (Fin n), ∀ᶠ m : K → ℤ in atTop,
        (NumbersDVR.hilbFn (mIdealOver F y) (m - ∑ i ∈ T, δ i) : ℚ) =
          eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p := fun T =>
      ((tendsto_atTop_add_const_right atTop (-(∑ i ∈ T, δ i)) tendsto_id).eventually hpH).mono
        fun m hm => by simpa only [id, sub_eq_add_neg] using hm
    filter_upwards [hMD, eventually_all.mpr h2] with m h1 h2
    rw [mixedDiff_eq_sum] at h1
    have h1' := congrArg (Int.cast : ℤ → ℚ) h1
    push_cast at h1'
    rw [← h1']
    exact Finset.sum_congr rfl fun T _ => by rw [h2 T]
  have hall := altSum_eq_of_eventually p δ (D : ℚ) hev

  have hsecs : ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in atTop,
      ((restrLen (primeOf (S := F) x)
          ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys F x (c : ℤ))) : ℤ) : ℚ) =
        eval (fun k => (((∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k : ℤ) : ℚ)) p := fun T => by
    filter_upwards [hT F K ι Ω y k₀ N e x hx hmod n L δ hL T, hpS (∑ i ∈ T, δ i)] with c h1 h2
    rw [restrLen_primeOf_eq_finrank x hj, h1, ← h2]
    simp
  have hfin : ∀ᶠ c : ℕ in atTop, interSum (primeOf (S := F) x) (fun i => (L i).toSubSystem) c = D := by
    filter_upwards [eventually_all.mpr hsecs] with c hc
    apply Int.cast_injective (α := ℚ)
    rw [interSum, ← hall (∑ i, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)]
    push_cast
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun T => ?_
    have hcard : Tᶜ.card = n - T.card := by rw [Finset.card_compl, Fintype.card_fin]
    have hvec : (∑ i, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) - ∑ i ∈ Tᶜ, δ i =
        ∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
      rw [← Finset.sum_add_sum_compl T δ]
      abel
    rw [hc T, hcard, hvec]
  unfold interNum
  exact (tendsto_const_nhds.congr' (hfin.mono fun c h => h.symm)).limUnder_eq

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHcSubsingletonOfBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart Cell CechC cellMon cechZc cechBc)

noncomputable section

def eulerChar (F : Type) [Field F] {K : Type} [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) : ℚ :=
  ∑ i ∈ Finset.range (∑ k, (Fintype.card (ι k) - 1) + 1),
    (-1 : ℚ) ^ i * (Module.finrank F (cechHc ι (quotPart F V) m i) : ℚ)

def EulerVar.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (v : Σ k, ι k),
    NumbersDVR.IsMultiHomogIdeal V →
    (∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F V) m i)) →
    (∀ (m : K → ℤ) (i : ℕ),
      FiniteDimensional F (cechHc ι (quotPart F (V.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}))) m i)) →
    (∀ (m : K → ℤ) (i : ℕ),
      FiniteDimensional F (cechHc ι (quotPart F (V ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) m i)) →
    ∀ m : K → ℤ, eulerChar F ι V m =
      eulerChar F ι (V.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) (m - Pi.single v.1 1) +
        eulerChar F ι (V ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) m

section Vanish

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

omit [Fintype K] [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in

theorem subsingleton_loc_of_block {V : Ideal (MvPolynomial (Σ k, ι k) F)} {k : K}
    (hk : ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ V) (I : ∀ k, Finset (ι k)) (hI : (I k).Nonempty) :
    Subsingleton (LocalizedModule (cellMon F I) (MvPolynomial (Σ k, ι k) F ⧸ V)) := by
  obtain ⟨i, hi⟩ := hI
  have ht : (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ cellMon F I :=
    Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hz : ∀ x : LocalizedModule (cellMon F I) (MvPolynomial (Σ k, ι k) F ⧸ V), x = 0 := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h a s =>
      rw [← LocalizedModule.zero_mk (1 : cellMon F I), LocalizedModule.mk_eq]
      refine ⟨⟨_, ht⟩, ?_⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      simp only [one_smul, smul_zero]
      rw [Submonoid.smul_def]
      change (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) • Ideal.Quotient.mk V a = 0
      rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact V.mul_mem_right _ (hk i)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem cechHc_subsingleton_of_block {V : Ideal (MvPolynomial (Σ k, ι k) F)} {k : K}
    (hk : ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ V) (m : K → ℤ) (n : ℕ) :
    Subsingleton (cechHc ι (quotPart F V) m n) := by
  have hI : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, Subsingleton (LocalizedModule (cellMon F I.1) (MvPolynomial (Σ k, ι k) F ⧸ V)) :=
    fun I => subsingleton_loc_of_block hk I.1 (I.2.1 k)
  have : Subsingleton (CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n) :=
    ⟨fun f g => funext fun I => (hI I).elim _ _⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

end Vanish

theorem EulerVar.hyps :
    let v : (Σ _ : Unit, Fin 1) := ⟨(), 0⟩
    let V : Ideal (MvPolynomial (Σ _ : Unit, Fin 1) ℚ) := Ideal.span {X v}
    NumbersDVR.IsMultiHomogIdeal V ∧
      (∀ (m : Unit → ℤ) (i : ℕ), FiniteDimensional ℚ (cechHc (fun _ : Unit => Fin 1) (quotPart ℚ V) m i)) ∧
      (∀ (m : Unit → ℤ) (i : ℕ), FiniteDimensional ℚ
        (cechHc (fun _ : Unit => Fin 1) (quotPart ℚ (V.colon (Ideal.span {(X v : MvPolynomial (Σ _ : Unit, Fin 1) ℚ)}))) m i)) ∧
      (∀ (m : Unit → ℤ) (i : ℕ), FiniteDimensional ℚ
        (cechHc (fun _ : Unit => Fin 1) (quotPart ℚ (V ⊔ Ideal.span {(X v : MvPolynomial (Σ _ : Unit, Fin 1) ℚ)})) m i)) := by
  intro v V
  have hX : (X v : MvPolynomial (Σ _ : Unit, Fin 1) ℚ) ∈ V := Ideal.subset_span rfl
  have hfin : ∀ W : Ideal (MvPolynomial (Σ _ : Unit, Fin 1) ℚ), (X v : MvPolynomial _ ℚ) ∈ W →
      ∀ (m : Unit → ℤ) (i : ℕ), FiniteDimensional ℚ (cechHc (fun _ : Unit => Fin 1) (quotPart ℚ W) m i) := by
    intro W hW m i
    have := cechHc_subsingleton_of_block (ι := fun _ : Unit => Fin 1) (V := W) (k := ())
      (fun j : Fin 1 => by rw [Subsingleton.elim j 0]; exact hW) m i
    have : Finite (cechHc (fun _ : Unit => Fin 1) (quotPart ℚ W) m i) := Finite.of_subsingleton
    exact Module.Finite.of_finite
  refine ⟨NumbersDVR.isMultiHomogIdeal_span_singleton
    (isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight (fun _ : Unit => Fin 1)) v), hfin V hX, hfin _ ?_,
    hfin _ (Ideal.mem_sup_left hX)⟩
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
  exact V.mul_mem_left _ hX

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellPosExact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

section

variable (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]

def CellPosExact (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) : Prop :=
  ∀ q : ℕ, ∀ s ∈ cellCOf S G (q + 1), cellD S y (q + 1) s = 0 →
    ∃ t ∈ cellCOf S G q, cellD S y q t = s

end

def CellContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (G : (∀ k, Finset (ι k)) → Submodule S Ω) (c : ∀ k, ι k),
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ¬ CellMeets y I → G I = ⊥) →
    (∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) → CellMeets y I' → G I ≤ G I') →
    (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → ∀ k,
      G (Function.update I k (insert (c k) (I k))) = G I) →
    CellPosExact S y G

theorem CellContract.hyps :
    (∀ k, (fun _ : (Σ _ : Unit, Fin 2) => (1 : ℚ)) ⟨k, (fun _ => (0 : Fin 2) : ∀ _ : Unit, Fin 2) k⟩ ≠ 0) ∧
    (∀ I : ∀ _ : Unit, Finset (Fin 2), (∀ k, (I k).Nonempty) →
      ¬ CellMeets (fun _ : (Σ _ : Unit, Fin 2) => (1 : ℚ)) I → (⊤ : Submodule ℚ ℚ) = ⊥) ∧
    (∀ I I' : ∀ _ : Unit, Finset (Fin 2), (∀ k, (I k).Nonempty) → (∀ k, I k ⊆ I' k) →
      CellMeets (fun _ : (Σ _ : Unit, Fin 2) => (1 : ℚ)) I' → (⊤ : Submodule ℚ ℚ) ≤ ⊤) ∧
    (∀ I : ∀ _ : Unit, Finset (Fin 2), (∀ k, (I k).Nonempty) → ∀ _ : Unit,
      (⊤ : Submodule ℚ ℚ) = ⊤) :=
  ⟨fun _ => one_ne_zero, fun _ _ h => absurd (fun _ _ _ => one_ne_zero) h, fun _ _ _ _ _ => le_rfl,
    fun _ _ _ => rfl⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPointOfSameModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

noncomputable section

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem subset_locIn_of_prime {A : Subalgebra S Ω} {p : Ideal A} [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  mem_locIn.mpr ⟨⟨a, ha⟩, 1, one_not_mem_of_prime hp, by simp⟩

theorem closure_locIn (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] :
    Subfield.closure (IndefiniteRowSideFullHecke.Kleiman2.locIn A p : Set Ω) = Subfield.closure (A : Set Ω) := by
  apply le_antisymm
  · rw [Subfield.closure_le]
    intro u hu
    obtain ⟨a, b, _, rfl⟩ := mem_locIn.mp hu
    exact div_mem (Subfield.subset_closure a.2) (Subfield.subset_closure b.2)
  · exact Subfield.closure_mono (fun a ha => subset_locIn_of_prime ha)

def toLocIn (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] : A →+* IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  (algebraMap A Ω).codRestrict _ (fun a => subset_locIn_of_prime a.2)

theorem isLocalization_locIn (A : Subalgebra S Ω) (p : Ideal A) [p.IsPrime] :
    letI := (toLocIn A p).toAlgebra
    IsLocalization.AtPrime (IndefiniteRowSideFullHecke.Kleiman2.locIn A p) p := by
  let _ := (toLocIn A p).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, hb⟩
    have hb' : b ∉ p := Ideal.mem_primeCompl_iff.mp hb
    refine IsUnit.of_mul_eq_one ⟨(b : Ω)⁻¹, mem_locIn.mpr ⟨1, b, hb', by simp⟩⟩ ?_
    apply Subtype.ext
    show (b : Ω) * (b : Ω)⁻¹ = 1
    exact mul_inv_cancel₀ (coe_ne_zero_of_not_mem hb')
  · rintro ⟨u, hu⟩
    obtain ⟨a, b, hb, rfl⟩ := mem_locIn.mp hu
    refine ⟨(a, ⟨b, Ideal.mem_primeCompl_iff.mpr hb⟩), ?_⟩
    apply Subtype.ext
    show (a : Ω) / b * b = a
    exact div_mul_cancel₀ _ (coe_ne_zero_of_not_mem hb)
  · intro x y h
    refine ⟨1, ?_⟩
    have h2 : ((algebraMap A (IndefiniteRowSideFullHecke.Kleiman2.locIn A p) x : IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : Ω) =
        ((algebraMap A (IndefiniteRowSideFullHecke.Kleiman2.locIn A p) y : IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : Ω) := by rw [h]
    have hxy : x = y := Subtype.ext h2
    rw [hxy]

theorem exists_point_of_sameModel {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι' k) → Ω} (h : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y y')
    {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (P : Ideal (chartRingOver S y c)) [hP : P.IsPrime] :
    ∃ c' : ∀ k, ι' k, (∀ k, y' ⟨k, c' k⟩ ≠ 0) ∧ ∃ P' : Ideal (chartRingOver S y' c'), P'.IsPrime ∧
      IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) P = IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y' c') P' := by
  have h' : IndefiniteRowSideFullHecke.Kleiman2.modelPts S y = IndefiniteRowSideFullHecke.Kleiman2.modelPts S y' := h
  have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) P ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts S y' := by
    rw [← h']
    exact ⟨c, hc, P, hP, rfl⟩
  obtain ⟨c', hc', P', hP', hzz⟩ := hz
  exact ⟨c', hc', P', hP', hzz⟩

theorem birational_of_sameModel {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι' k) → Ω} (h : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y y')
    (hb : IndefiniteRowSideFullHecke.Kleiman2.IsBirational S y') : IndefiniteRowSideFullHecke.Kleiman2.IsBirational S y := by
  intro c hc
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (chartRingOver S y c)
  have := hP.isPrime
  obtain ⟨c', hc', P', hP', hzz⟩ := exists_point_of_sameModel h hc P
  have := hP'
  rw [← closure_locIn _ P, hzz, closure_locIn]
  exact hb c' hc'

theorem normal_of_sameModel {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι' k) → Ω} (h : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y y')
    (hn : IndefiniteRowSideFullHecke.Kleiman2.IsNormalModel S y') : IndefiniteRowSideFullHecke.Kleiman2.IsNormalModel S y := by
  intro c hc
  refine @IsIntegrallyClosed.of_isLocalization_maximal _ _
    (fun P _ => IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) P) (fun _ _ => inferInstance)
    (fun P _ => (toLocIn _ P).toAlgebra) (fun P _ => isLocalization_locIn _ P) inferInstance
    (fun P _ => ?_)
  obtain ⟨c', hc', P', hP', hzz⟩ := exists_point_of_sameModel h hc P
  have := hP'
  have := hn c' hc'
  let _ := (toLocIn (chartRingOver S y' c') P').toAlgebra
  have := isLocalization_locIn (chartRingOver S y' c') P'
  show IsIntegrallyClosed (IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S y c) P)
  rw [hzz]
  exact isIntegrallyClosed_of_isLocalization _ P'.primeCompl P'.primeCompl_le_nonZeroDivisors

theorem ModelInvariants.full : ModelInvariants.Statement := by
  intro S _ Ω _ _ K _ ι _ K' _ ι' _ y y' _ _ h
  have hs : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y' y := Eq.symm h
  exact ⟨⟨birational_of_sameModel hs, birational_of_sameModel h⟩,
    ⟨normal_of_sameModel hs, normal_of_sameModel h⟩⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

