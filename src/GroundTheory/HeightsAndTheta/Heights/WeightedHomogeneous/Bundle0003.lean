import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AddBlockEquivSymmChartRingMap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal mConeMap)

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace AddBlockEq

def toIndefiniteRowSideFullHecke {P : ArithVariety n} (D : GroundTheory.Heights₂.Heights.AddBlockData P) : AddBlockData P where
  deg := D.deg
  m := D.size
  x j := funFieldEquiv P (D.elt j)
  homog j := (isOfDegree_iff P D.deg (D.elt j)).1 (D.elt_deg j)
  chart c hc j := by
    have h := (funFieldEquiv_mem_chartRing_iff P c _).2 (D.chart_mem c hc j)
    rwa [map_div₀, funFieldEquiv_chartPow, div_eq_mul_inv, ← chartPow_neg] at h
  unit c hc := by
    obtain ⟨u, hu, hsum⟩ := D.generating c hc
    refine ⟨fun j ↦ funFieldEquiv P (u j), fun j ↦ (funFieldEquiv_mem_chartRing_iff P c _).2 (hu j), ?_⟩
    have h := congrArg (funFieldEquiv P) hsum
    simpa only [map_sum, map_mul, map_div₀, map_inv₀, map_one, funFieldEquiv_chartPow, div_eq_mul_inv,
      chartPow_neg] using h

def split_model_to_place_model {P : ArithVariety n} (D : AddBlockData P) : GroundTheory.Heights₂.Heights.AddBlockData P where
  deg := D.deg
  size := D.m
  elt j := (funFieldEquiv P).symm (D.x j)
  elt_deg j := by
    rw [isOfDegree_iff, RingEquiv.apply_symm_apply]
    exact D.homog j
  chart_mem c hc j := by
    rw [← funFieldEquiv_mem_chartRing_iff, map_div₀, funFieldEquiv_chartPow, RingEquiv.apply_symm_apply,
      div_eq_mul_inv, ← chartPow_neg]
    exact D.chart c hc j
  generating c hc := by
    obtain ⟨u, hu, hsum⟩ := D.unit c hc
    refine ⟨fun j ↦ (funFieldEquiv P).symm (u j), fun j ↦ ?_, ?_⟩
    · rw [← funFieldEquiv_mem_chartRing_iff, RingEquiv.apply_symm_apply]
      exact hu j
    · apply (funFieldEquiv P).injective
      simpa only [map_sum, map_mul, map_div₀, map_inv₀, map_one, funFieldEquiv_chartPow, div_eq_mul_inv,
        chartPow_neg, RingEquiv.apply_symm_apply] using hsum

def addBlockEquiv (P : ArithVariety n) :
    GroundTheory.Heights₂.Heights.AddBlockData P ≃ AddBlockData P where
  toFun := toIndefiniteRowSideFullHecke
  invFun := split_model_to_place_model
  left_inv D := by
    cases D
    simp only [toIndefiniteRowSideFullHecke, split_model_to_place_model, RingEquiv.symm_apply_apply]
  right_inv D := by
    cases D
    simp only [toIndefiniteRowSideFullHecke, split_model_to_place_model, RingEquiv.apply_symm_apply]

section Ext

variable {P : ArithVariety n} (D : GroundTheory.Heights₂.Heights.AddBlockData P)

theorem addBlockEquiv_genericPoint (v : Coord D.extSizes) : (toIndefiniteRowSideFullHecke D).yPlus v = funFieldEquiv P (D.extVal v) := by
  rcases v with ⟨_ | k, i⟩
  · rfl
  · exact (funFieldEquiv_mkF P _).symm

theorem coneMap_addBlockEquiv (f : MvPolynomial (Coord D.extSizes) ℤ) :
    mConeMap (toIndefiniteRowSideFullHecke D).yPlus f =
      MvPolynomial.map (funFieldEquiv P : P.FunField →+* FunField P) (D.extMap f) := by
  change aeval (fun p : Coord D.extSizes ↦ C ((toIndefiniteRowSideFullHecke D).yPlus p) * X p.1) f = _
  induction f using MvPolynomial.induction_on with
  | C r => simp [GroundTheory.Heights₂.Heights.AddBlockData.extMap]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [GroundTheory.Heights₂.Heights.AddBlockData.extMap, addBlockEquiv_genericPoint]

theorem addBlockEquiv_extIdeal : (toIndefiniteRowSideFullHecke D).ext = D.extIdeal := by
  ext f
  have h := coneMap_addBlockEquiv D f
  change mConeMap (toIndefiniteRowSideFullHecke D).yPlus f = 0 ↔ D.extMap f = 0
  constructor
  · intro h0
    exact MvPolynomial.map_injective _ (funFieldEquiv P).injective
      ((h.symm.trans h0).trans (map_zero _).symm)
  · intro h0
    exact h.trans (by rw [h0, map_zero])

theorem extPoints_eq : D.extPoints = conePoints (toIndefiniteRowSideFullHecke D).ext ℂ := by
  rw [addBlockEquiv_extIdeal]
  rfl

theorem addBlockEquiv_join {F : Type*} (z : Cone n F) (z' : Fin (D.size + 1) → F) :
    (toIndefiniteRowSideFullHecke D).join z z' = D.joinPt z z' := by
  funext o
  cases o <;> rfl

end Ext

section OfTwin

variable {P : ArithVariety n} (D : AddBlockData P)

theorem addBlockEquiv_symm_genericPoint : (toIndefiniteRowSideFullHecke (split_model_to_place_model D)).yPlus = D.yPlus := by
  funext v
  rcases v with ⟨_ | k, i⟩
  · exact RingEquiv.apply_symm_apply _ _
  · rfl

theorem addBlockEquiv_symm_extIdeal : (split_model_to_place_model D).extIdeal = D.ext :=
  (addBlockEquiv_extIdeal (split_model_to_place_model D)).symm.trans (congrArg mCoordIdeal (addBlockEquiv_symm_genericPoint D))

theorem addBlockEquiv_symm_conePoints : (split_model_to_place_model D).extPoints = conePoints D.ext ℂ := by
  rw [extPoints_eq, addBlockEquiv_extIdeal, addBlockEquiv_symm_extIdeal]
  rfl

end OfTwin

end AddBlockEq

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}

namespace AddBlockData

def ofObjects (D : Heights.AddBlockData P) : AddBlockData P where
  deg := D.deg
  m := D.size
  x j := funFieldEquiv P (D.elt j)
  homog j := (isOfDegree_iff P D.deg (D.elt j)).1 (D.elt_deg j)
  chart c hc j := by
    rw [← funFieldEquiv_div_chartPow, funFieldEquiv_mem_chartRing_iff]
    exact D.chart_mem c hc j
  unit c hc := by
    obtain ⟨u, hu, hsum⟩ := D.generating c hc
    refine ⟨fun j ↦ funFieldEquiv P (u j), fun j ↦ (funFieldEquiv_mem_chartRing_iff P c _).2 (hu j),
      ?_⟩
    simp only [← funFieldEquiv_div_chartPow, ← map_mul, ← map_sum, hsum, map_one]

def toObjects (D : AddBlockData P) : Heights.AddBlockData P where
  deg := D.deg
  size := D.m
  elt j := (funFieldEquiv P).symm (D.x j)
  elt_deg j := (isOfDegree_iff P D.deg _).2 (by rw [RingEquiv.apply_symm_apply]; exact D.homog j)
  chart_mem c hc j := by
    rw [← funFieldEquiv_mem_chartRing_iff, funFieldEquiv_div_chartPow, RingEquiv.apply_symm_apply]
    exact D.chart c hc j
  generating c hc := by
    obtain ⟨u, hu, hsum⟩ := D.unit c hc
    refine ⟨fun j ↦ (funFieldEquiv P).symm (u j), fun j ↦ ?_, ?_⟩
    · rw [← funFieldEquiv_mem_chartRing_iff, RingEquiv.apply_symm_apply]
      exact hu j
    · apply (funFieldEquiv P).injective
      simp only [map_sum, map_mul, funFieldEquiv_div_chartPow, RingEquiv.apply_symm_apply, map_one]
      exact hsum

theorem ofObjects_toObjects (D : AddBlockData P) : ofObjects (toObjects D) = D := by
  rcases D with ⟨deg, m, x, _, _, _⟩
  simp only [toObjects, ofObjects, RingEquiv.apply_symm_apply]

theorem ξ_ofObjects (D : Heights.AddBlockData P) (c : (k : ι) → Fin (n k + 1))
    (j : Fin (D.size + 1)) : (ofObjects D).ξ c j = funFieldEquiv P (D.xi c j) := by
  show funFieldEquiv P (D.elt j) * chartPow P c (-D.deg) =
    funFieldEquiv P (D.elt j / P.chartPow c D.deg)
  rw [funFieldEquiv_div_chartPow]

end AddBlockData

open _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.AddBlockData

omit [Fintype ι] in

theorem isWeightedHomogeneous_toNat {f : MvPolynomial (Coord n) ℤ} {d : ι → ℕ} {a : ι → ℤ}
    (h : ∃ δ : ι → ℕ, IsWeightedHomogeneous (coordDeg n) f δ ∧ ∀ k, (δ k : ℤ) = d k + a k) :
    IsWeightedHomogeneous (coordDeg n) f (fun k ↦ ((d k : ℤ) + a k).toNat) := by
  obtain ⟨δ, hδ, hδk⟩ := h
  have e : (fun k ↦ ((d k : ℤ) + a k).toNat) = δ := by
    funext k
    have := hδk k
    omega
  rw [e]
  exact hδ

namespace ChartForms

variable {D : AddBlockData P}

theorem isFormSystem (G : ChartForms D) : (toObjects D).IsFormSystem G.d G.g where
  pos := G.d_pos
  nonneg := G.dn_nonneg
  homog c j := by
    refine ⟨fun k ↦ ((G.d k : ℤ) + D.deg k).toNat, ?_, fun k ↦ ?_⟩
    · by_cases hc : IsLive P c
      · exact G.g_homog c hc j
      · rw [G.g_dead c hc j]
        exact isWeightedHomogeneous_zero ℤ _ _
    · have := G.dn_nonneg k
      show (((G.d k : ℤ) + D.deg k).toNat : ℤ) = G.d k + D.deg k
      omega
  value c hc j := by
    apply (funFieldEquiv P).injective
    rw [map_mul, funFieldEquiv_mkF, funFieldEquiv_mkF]
    exact (G.g_val c hc j).trans (congrArg _ (RingEquiv.apply_symm_apply _ _).symm)
  dead c hc j := G.g_dead c hc j

theorem isFormSystem_ofObjects {D : Heights.AddBlockData P} (G : ChartForms (ofObjects D)) :
    D.IsFormSystem G.d G.g where
  pos := G.d_pos
  nonneg := G.dn_nonneg
  homog c j := G.isFormSystem.homog c j
  value c hc j := by
    apply (funFieldEquiv P).injective
    rw [map_mul, funFieldEquiv_mkF, funFieldEquiv_mkF]
    exact G.g_val c hc j
  dead c hc j := G.g_dead c hc j

def ofFormSystem {D : Heights.AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (h : D.IsFormSystem d g) : ChartForms (ofObjects D) where
  d := d
  d_pos := h.pos
  dn_nonneg := h.nonneg
  g := g
  g_homog c _ j := isWeightedHomogeneous_toNat (h.homog c j)
  g_val c hc j := by
    show val P (g c j) = val P (chartMonomial c d) * funFieldEquiv P (D.elt j)
    rw [← funFieldEquiv_mkF, ← funFieldEquiv_mkF, ← map_mul, h.value c hc j]
  g_dead c hc j := h.dead c hc j

def ofToObjects {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.m + 1) → MvPolynomial (Coord n) ℤ}
    (h : (toObjects D).IsFormSystem d g) : ChartForms D where
  d := d
  d_pos := h.pos
  dn_nonneg := h.nonneg
  g := g
  g_homog c _ j := isWeightedHomogeneous_toNat (h.homog c j)
  g_val c hc j := by
    have e := congrArg (funFieldEquiv P) (h.value c hc j)
    rw [map_mul, funFieldEquiv_mkF, funFieldEquiv_mkF] at e
    rw [e]
    exact congrArg _ (RingEquiv.apply_symm_apply _ _)
  g_dead c hc j := h.dead c hc j

end ChartForms

theorem isFormSystem_iff_exists_chartForms (D : Heights.AddBlockData P) (d : ι → ℕ)
    (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ) :
    D.IsFormSystem d g ↔ ∃ G : ChartForms (ofObjects D), G.d = d ∧ G.g = g := by
  constructor
  · intro h
    exact ⟨ChartForms.ofFormSystem h, rfl, rfl⟩
  · rintro ⟨G, rfl, rfl⟩
    exact G.isFormSystem_ofObjects

theorem exists_chartForms_iff_isFormSystem (D : AddBlockData P) (d : ι → ℕ)
    (g : ((k : ι) → Fin (n k + 1)) → Fin (D.m + 1) → MvPolynomial (Coord n) ℤ) :
    (∃ G : ChartForms D, G.d = d ∧ G.g = g) ↔ (toObjects D).IsFormSystem d g := by
  constructor
  · rintro ⟨G, rfl, rfl⟩
    exact G.isFormSystem
  · intro h
    exact ⟨ChartForms.ofToObjects h, rfl, rfl⟩

section Metric

variable {D : AddBlockData P}

theorem den_eq (G : ChartForms D) (Γ : GenSystem P) :
    den G Γ = (toObjects D).den G.d G.g Γ.f Γ.δ := rfl

theorem den_ofFormSystem {D : Heights.AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (h : D.IsFormSystem d g) {r : ℕ} {f : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ}
    (hf : P.IsHomogGenerators f δ) :
    D.den d g f δ = den (ChartForms.ofFormSystem h) (GenSystem.ofIsHomogGenerators hf) := rfl

end Metric

omit [DecidableEq ι] in

theorem hermLine_pow_metric (A : HermLine n) (m : ℕ) (z : Cone n ℂ) :
    (A.pow m).metric z = A.metric z ^ m := rfl

example (k₀ : ι) (e : ℕ) :
    (toObjects (powBlock n k₀ e)).IsFormSystem (powChartForms n k₀ e).d (powChartForms n k₀ e).g :=
  (powChartForms n k₀ e).isFormSystem

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.OneBlockIdealEqComapProjIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

theorem hermLine_eq_of {A B : HermLine n} (hdeg : A.deg = B.deg) (hmet : A.metric = B.metric) :
    A = B := by
  cases A
  cases B
  cases hdeg
  cases hmet
  rfl

omit [DecidableEq ι] in

theorem powDivStd_eq (M : HermLine n) (k : ℕ) :
    powDivStd M k = (M.pow k).mul (HermLine.standard n).inv := by
  refine hermLine_eq_of ?_ ?_
  · funext b
    change (k : ℤ) * M.deg b - 1 = k • M.deg b + -1
    rw [nsmul_eq_mul, sub_eq_add_neg]
  · funext z
    change M.metric z ^ k / (HermLine.standard n).metric z =
      M.metric z ^ k * ((HermLine.standard n).metric z)⁻¹
    rw [div_eq_mul_inv]

omit [DecidableEq ι] in

theorem twistPow_eq (M : HermLine n) (p a : ℕ) (C : ℝ) :
    twistPow M p a C =
      (((M.pow p).mul (HermLine.standard n)).pow a).scale (Real.exp (-(a * C))) (Real.exp_pos _) := by
  refine hermLine_eq_of ?_ ?_
  · funext b
    change (a : ℤ) * (p * M.deg b + 1) = a • (p • M.deg b + 1)
    simp only [nsmul_eq_mul]
  · rfl

omit [DecidableEq ι] in

theorem twistPow_deg (M : HermLine n) (p a : ℕ) (C : ℝ) :
    (twistPow M p a C).deg = a • (p • M.deg + (HermLine.standard n).deg) := by
  rw [twistPow_eq]
  rfl

omit [DecidableEq ι] in

theorem twistPow_metric (M : HermLine n) (p a : ℕ) (C : ℝ) (z : Cone n ℂ) :
    (twistPow M p a C).metric z =
      Real.exp (-(a * C)) * (((M.pow p).mul (HermLine.standard n)).pow a).metric z := by
  rw [twistPow_eq]
  rfl

theorem funFieldEquiv_toFun {P : ArithVariety n} {a : ι → ℤ} (e : IntegralSection P a) :
    funFieldEquiv P e.toFun = sectionVal e := by
  rw [IntegralSection.toFun, map_div₀, funFieldEquiv_mkF, funFieldEquiv_mkF]
  rfl

theorem toFun_eq_symm_sectionVal {P : ArithVariety n} {a : ι → ℤ} (e : IntegralSection P a) :
    e.toFun = (funFieldEquiv P).symm (sectionVal e) := by
  rw [← funFieldEquiv_toFun, RingEquiv.symm_apply_apply]

def blockCoordEquiv (k₀ : ι) : Fin (n k₀ + 1) ≃ Coord (fun _ : Unit ↦ n k₀) where
  toFun i := ⟨(), i⟩
  invFun v := v.2
  left_inv _ := rfl
  right_inv := fun ⟨(), _⟩ ↦ rfl

omit [Fintype ι] in

theorem oneBlockIdeal_eq_comap_projIdeal (P : ArithVariety n) (k₀ : ι) :
    oneBlockIdeal P k₀ = (P.projIdeal k₀).comap (rename (blockCoordEquiv (n := n) k₀)) := by
  ext f
  rw [oneBlockIdeal, ArithVariety.projIdeal, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap,
    rename_rename]
  rfl

omit [Fintype ι] in

theorem mem_oneBlockPoints_iff (P : ArithVariety n) (k₀ : ι) (w : Fin (n k₀ + 1) → ℂ) :
    w ∈ oneBlockPoints P k₀ ↔
      (fun _ : Unit ↦ w) ∈ Heights.conePoints (P.projIdeal k₀) ℂ := by
  have heval : ∀ f : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
      evalCone (fun _ : Unit ↦ w) f =
        eval₂ (Int.castRingHom ℂ) w (rename (blockCoordEquiv (n := n) k₀).symm f) := by
    intro f
    rw [evalCone, eval₂_rename]
    rfl
  constructor
  · rintro ⟨hw, hf⟩
    refine ⟨fun _ ↦ hw, fun f hfI ↦ ?_⟩
    rw [heval]
    refine hf _ ?_
    rw [oneBlockIdeal_eq_comap_projIdeal, Ideal.mem_comap, rename_rename, Equiv.self_comp_symm,
      rename_id_apply]
    exact hfI
  · rintro ⟨hw, hf⟩
    refine ⟨hw (), fun f hfI ↦ ?_⟩
    rw [oneBlockIdeal_eq_comap_projIdeal, Ideal.mem_comap] at hfI
    have h := hf _ hfI
    rw [heval, rename_rename, Equiv.symm_comp_self, rename_id_apply] at h
    exact h

omit [DecidableEq ι] in

theorem pullFS_metric (k₀ : ι) (z : Cone n ℂ) :
    (pullFS n k₀).metric z =
      (HermLine.standard (fun _ : Unit ↦ n k₀)).metric (Heights.projBlock k₀ z) := rfl

omit [DecidableEq ι] in

theorem pullFS_metric_eq_l2Norm (k₀ : ι) (z : Cone n ℂ) :
    (pullFS n k₀).metric z = l2Norm (z k₀) := by
  rw [pullFS_metric]
  change ∏ _u : Unit, l2Norm (z k₀) = _
  rw [Fintype.prod_unique]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

