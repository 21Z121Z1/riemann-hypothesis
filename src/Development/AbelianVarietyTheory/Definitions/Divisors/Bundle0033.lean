import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def htInf (y : GL (Fin a) (Cinf E)) : ℝ :=
  ∏ w : InfinitePlace E, htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y)

def kerInf {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (F : GA E a → ℂ) (g : GA E a) : ℂ := ∫ x, k x * F (g * infGL E a (γ x)) ∂ν

def rspan (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  sInf {S | (∀ φ ∈ π.V, φ.1 ∈ S) ∧ (∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S) ∧
    (∀ F ∈ S, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ S)}

theorem mem_rspan {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V) : φ.1 ∈ rspan π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ h

theorem rt_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) (h : GA E a) :
    (fun g => F (g * h)) ∈ rspan π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem kerInf_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ rspan π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X ν k γ hk

theorem rspan_le {π : CuspSub E a} {S : Submodule ℂ (GA E a → ℂ)} (h₁ : ∀ φ ∈ π.V, φ.1 ∈ S)
    (h₂ : ∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S)
    (h₃ : ∀ F ∈ S, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ S) : rspan π ≤ S :=
  sInf_le ⟨h₁, h₂, h₃⟩

theorem one_le_htInf (y : GL (Fin a) (Cinf E)) : 1 ≤ htInf y := by
  unfold htInf
  calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem htInf_pos (y : GL (Fin a) (Cinf E)) : 0 < htInf y := lt_of_lt_of_le one_pos (one_le_htInf y)

theorem htGL_le_htInf (y : GL (Fin a) (Cinf E)) (w : InfinitePlace E) :
    htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y) ≤ htInf y := by
  classical
  unfold htInf
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  refine le_mul_of_one_le_right (htGL_pos _).le ?_
  calc (1 : ℝ) = ∏ _w ∈ Finset.univ.erase w, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem norm_entry_le_htInf (y : GL (Fin a) (Cinf E)) (i j : Fin a) (w : InfinitePlace E) :
    ‖(y : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ≤ htInf y ∧
      ‖((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ≤ htInf y := by
  set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ := Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
  refine ⟨(norm_entry_le_htGL (p y) i j).trans (htGL_le_htInf y w), ?_⟩
  have e : ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w =
      (((p y)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j := by
    rw [← map_inv]; rfl
  rw [e]
  exact (norm_entry_le_htGL _ i j).trans ((htGL_inv (p y)).le.trans (htGL_le_htInf y w))

theorem height_le_htInf (y : GL (Fin a) (Cinf E)) : height y ≤ 3 * htInf y := by
  have h0 := (htInf_pos y).le
  have h1 : ‖toL y.val‖ ≤ htInf y :=
    pi_norm_le_iff_of_nonneg h0 |>.2 fun i => pi_norm_le_iff_of_nonneg h0 |>.2 fun j =>
      pi_norm_le_iff_of_nonneg h0 |>.2 fun w => (norm_entry_le_htInf y i j w).1
  have h2 : ‖toL (y⁻¹).val‖ ≤ htInf y :=
    pi_norm_le_iff_of_nonneg h0 |>.2 fun i => pi_norm_le_iff_of_nonneg h0 |>.2 fun j =>
      pi_norm_le_iff_of_nonneg h0 |>.2 fun w => (norm_entry_le_htInf y i j w).2
  unfold height
  linarith [one_le_htInf y]

theorem IsRapidInf.of_htInf {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : Measurable k) (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)) i j)
    (hm : ∀ N : ℕ, Integrable (fun x => ‖k x‖ * htInf (γ x) ^ N) ν) : IsRapidInf ν k γ := by
  refine ⟨hk, measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hγ i j, fun N => ?_⟩
  refine ((hm N).const_mul (3 ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (hk.norm.mul ?_).aestronglyMeasurable
    have hm' : Measurable fun x => toL (γ x).val :=
      measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hγ i j
    have hi : Measurable fun x => toL ((γ x)⁻¹).val := by
      refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun w => ?_
      set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ :=
        Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
      have e : (fun x => toL ((γ x)⁻¹).val i j w) =
          fun x => (((p (γ x))⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j := by
        funext x
        rw [← map_inv]; rfl
      rw [e]
      exact measurable_comp_GL (F := fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)
        ((Units.continuous_coe_inv : Continuous fun g : GL (Fin a) ℂ =>
          ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)).matrix_elem i j)
        fun i' j' => (measurable_pi_apply w).comp (hγ i' j')
    unfold height
    exact ((measurable_const.add hm'.norm).add hi.norm).pow_const N
  · have h0 : 0 ≤ height (γ x) := by unfold height; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖k x‖ * height (γ x) ^ N ≤ ‖k x‖ * (3 * htInf (γ x)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (height_le_htInf _) N) (norm_nonneg _)
      _ = 3 ^ N * (‖k x‖ * htInf (γ x) ^ N) := by rw [mul_pow]; ring

theorem measurable_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) : Measurable (chart φ g) := by
  classical
  have e : chart φ g = (invSet E a).piecewise (chart φ g) (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ invSet E a
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      exact dif_neg hx
  rw [e]
  exact (hφ g).continuousOn.measurable_piecewise continuousOn_const isOpen_invSet.measurableSet

theorem measurable_comp_infGL {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun x => φ (g * infGL E a (γ x)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun x => φ (g * infGL E a (γ x))) = fun x => chart φ g (toL (γ x).val) :=
    funext fun x => (chart_val φ g (γ x)).symm
  rw [e]
  exact (measurable_chart hφ g).comp h

theorem IsRapidInf.integrable {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) {g : GA E a}
    (hg : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) :
    Integrable (fun x => k x * φ (g * infGL E a (γ x))) ν := by
  obtain ⟨C, N, hC⟩ := hg
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by unfold height; positivity) N
    exact nonneg_of_mul_nonneg_left h hp
  refine ((hk.2.2 N).const_mul C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hk.1.mul (measurable_comp_infGL hφ g hk.2.1)).aestronglyMeasurable
  · rw [norm_mul]
    calc ‖k x‖ * ‖φ (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
          mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
      _ = C * (‖k x‖ * height (γ x) ^ N) := by ring

theorem rspan_ne_bot (π : CuspSub E a) : rspan π ≠ ⊥ := by
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  intro hb
  have h := mem_rspan hφ
  rw [hb, Submodule.mem_bot] at h
  exact h0 (Subtype.ext h)

theorem rspan_le_leftInv (π : CuspSub E a) : rspan π ≤ SpanModel.leftInv E a := by
  refine rspan_le (fun φ hφ => (π.cusp φ hφ).1.left) (fun F hF h γ g => ?_) fun F hF X _ ν _ k γ _ γ' g => ?_
  · change F (ratGL E a γ * g * h) = F (g * h)
    rw [mul_assoc]; exact hF γ _
  · change kerInf ν k γ F (ratGL E a γ' * g) = kerInf ν k γ F g
    simp only [kerInf, mul_assoc]
    congr 1
    funext x
    rw [hF γ']

theorem rspan_left (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ rspan π) (γ : GL (Fin a) E) (g : GA E a) :
    F (ratGL E a γ * g) = F g :=
  rspan_le_leftInv π hF γ g

theorem rspan_eq_mspanR (π : CuspSub E a) : rspan π = mspanR π := by
  refine le_antisymm (rspan_le ?_ ?_ ?_) ?_
  · exact fun φ hφ => Submodule.mem_sInf.2 fun _ hS => hS.1 φ hφ
  · exact fun F hF h => Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h
  · exact fun F hF X _ ν _ k γ hk => Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X _ ν inferInstance k γ hk
  · refine sInf_le ⟨fun φ hφ => mem_rspan hφ, fun F hF h => rt_mem_rspan hF h, fun F hF X _ ν _ k γ hk => ?_⟩
    exact kerInf_mem_rspan hF ν hk

open Classical in

def plS (w : InfinitePlace E) : ℂ →ₙ+* Cinf E where
  toFun z := Pi.single w z
  map_mul' z z' := by ext w'; by_cases h : w' = w <;> simp [Pi.single_apply, h]
  map_zero' := by ext w'; simp [Pi.single_apply]
  map_add' z z' := by ext w'; by_cases h : w' = w <;> simp [Pi.single_apply, h]

def plGL (w : InfinitePlace E) : GL (Fin a) ℂ →* GL (Fin a) (Cinf E) := cornerGL a (plS w)

open Classical in

theorem plGL_apply (w : InfinitePlace E) (g : GL (Fin a) ℂ) (i j : Fin a) (w' : InfinitePlace E) :
    (plGL w g : Matrix (Fin a) (Fin a) (Cinf E)) i j w' =
      if w' = w then (g : Matrix (Fin a) (Fin a) ℂ) i j else (1 : Matrix (Fin a) (Fin a) ℂ) i j := by
  change (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w' - (Pi.single w ((1 : Matrix (Fin a) (Fin a) ℂ) i j) : Cinf E) w' +
    (Pi.single w ((g : Matrix (Fin a) (Fin a) ℂ) i j) : Cinf E) w' = _
  simp only [Pi.single_apply, Matrix.one_apply]
  split_ifs <;> simp_all

open Classical in

theorem map_plGL (w : InfinitePlace E) (g : GL (Fin a) ℂ) (w' : InfinitePlace E) :
    Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w') (plGL w g) =
      if w' = w then g else 1 := by
  classical
  ext i j
  change (plGL w g : Matrix (Fin a) (Fin a) (Cinf E)) i j w' = _
  rw [plGL_apply]
  split_ifs <;> rfl

theorem isRapidInf_dirac (y : GL (Fin a) (Cinf E)) :
    IsRapidInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) :=
  ⟨measurable_const, measurable_const, fun _ => integrable_const _⟩

theorem kerInf_dirac (y : GL (Fin a) (Cinf E)) (F : GA E a → ℂ) (g : GA E a) :
    kerInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) F g = F (g * infGL E a y) := by
  simp [kerInf]

example (π : CuspSub E a) : 1 ≤ htInf (1 : GL (Fin a) (Cinf E)) ∧ rspan π ≠ ⊥ := ⟨one_le_htInf 1, rspan_ne_bot π⟩

example (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ rspan π) (y : GL (Fin a) (Cinf E)) :
    (fun g => F (g * infGL E a y)) ∈ rspan π := by
  have h := kerInf_mem_rspan hF (Measure.dirac ()) (isRapidInf_dirac y)
  rwa [show kerInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) F = fun g => F (g * infGL E a y) from
    funext (kerInf_dirac y F)] at h

example (w : InfinitePlace E) : htInf (plGL (a := a) w 1) = htGL (1 : GL (Fin a) ℂ) ^ Fintype.card (InfinitePlace E) := by
  rw [map_one]
  unfold htInf
  simp

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MuGeOfMuLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel

noncomputable section

namespace GlobalTheory.MBLow

section Lat

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

def MuGe (h : HermFam K (Fin m → K)) (E : Submodule (𝓞 K) (Fin m → K)) (ν : ℝ) : Prop :=
  ∀ V : Submodule K (Fin m → K), ((m : ℝ) - Module.finrank K V) * ν ≤ deg h E - deg h (E ⊓ V.restrictScalars (𝓞 K))

def JetSysLow (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) (n : ℕ) (ν : ℝ)
    (β : ℕ → (K →+* ℂ) → ℝ) : Prop :=
  ∃ (r : ℕ) (hE : HermFam K (Fin r → K)) (E : Submodule (𝓞 K) (Fin r → K)) (Vf : ℕ → Submodule K (Fin r → K))
    (j : ℕ → (Fin r → K) →ₗ[K] K), Full E ∧ MuGe hE E ν ∧ Vf 0 = ⊤ ∧ ∀ i ≤ n,
      Vf (i + 1) = Vf i ⊓ LinearMap.ker (j i) ∧ (∃ v ∈ Vf i, j i v ≠ 0) ∧
      (∀ v ∈ E, v ∈ Vf i → ∀ a : K, a • x ∈ L → IsIntegral ℤ (a ^ i * j i v)) ∧
      ∀ (σ : K →+* ℂ) (q : ℕ) (v : Fin q → Fin r → K) (c : Fin q → ℂ), (∀ a, v a ∈ Vf i) →
        ‖∑ a, c a * σ (j i (v a))‖ ^ 2 ≤
          (β i σ * h.nrm σ x ^ i) ^ 2 * (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * hE.form σ (v a) (v b)).re

end Lat

def IsWeak {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp K)} {AA : Over (Sp (𝓞 K))} [GrpObj AA] [IsCommMonObj AA]
    {φ : P.A.left ⟶ AA.left} {MM : RigLB AA} {n : ℕ} (w : LB.Iso (MM.L.pull φ) (lbPow P.L n)) : Prop :=
  IsSemiAbelian AA ∧ IsGrpPullback P.A AA (spMap (algebraMap (𝓞 K) K)) φ ∧ Nonempty (CubicalStr AA MM) ∧ w.IsGen

def IsOver {K : Type} [Field K] [NumberField K] (F : SemiFib K) {K'' : Type} [Field K''] [NumberField K''] [Algebra K K'']
    {P : Out.PolAV (Sp K'')} (ψ : P.A.left ⟶ F.P₀.A.left) {AA : Over (Sp (𝓞 K''))} [GrpObj AA]
    (φ : P.A.left ⟶ AA.left) : Prop :=
  IsPolFibre (algebraMap K K'') F.P₀ P ψ ∧ ∃ j : AA.left ⟶ F.G.left,
    IsGrpPullback AA F.G (spMap (algebraMap (𝓞 K) (𝓞 K''))) j ∧ φ ≫ j = ψ ≫ F.φ

def SectionsLow : Prop := ∀ g : ℕ, 0 < g → ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g = g →
  ∀ h : HermFam K (Fin F.P₀.g → K), F.IsHerm h → ∀ m : ℕ, 1 ≤ m →
  ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'],
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra K' K'') (_ : Algebra K K'') (_ : IsScalarTower K K' K'')
      (P : Out.PolAV (Sp K'')) (ψ : P.A.left ⟶ F.P₀.A.left) (AA : Over (Sp (𝓞 K''))) (_ : GrpObj AA) (_ : IsCommMonObj AA)
      (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (w : LB.Iso (MM.L.pull φ) (lbPow P.L (4 * m ^ 2))) (r : ℕ)
      (b : Fin r → (lbPow P.L (4 * m ^ 2)).Sec) (E : Submodule (𝓞 K'') (Fin r → K'')) (hE : HermFam K'' (Fin r → K'')),
      IsOver F ψ φ ∧ IsWeak w ∧ Function.Bijective (fun c : Fin r → K'' => secComb P.A.hom c b) ∧
      (∀ c ∈ E, ∃ t : MM.L.Sec, SecMaps w (secPull t φ) (secComb P.A.hom c b)) ∧
      IsThetaMeanSquareNorm w b hE F.P₀.g ∧ Full E ∧ MuGe hE E (-F.falt h / 2 - C)

def SecJetsLow : Prop := ∀ g : ℕ, 0 < g → ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g = g →
  ∀ (h : HermFam K (Fin F.P₀.g → K)) (ρ : (K →+* ℂ) → ℝ), F.IsHerm h → F.IsRho ρ →
  ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (x : Fin F.P₀.g → K'), x ≠ 0 → ∀ n : ℕ, 2 ≤ n →
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra K' K'') (_ : Algebra K K'') (_ : IsScalarTower K K' K'')
      (h'' : HermFam K'' (Fin F.P₀.g → K'')), IsBC h h'' ∧
      JetSysLow h'' (latBC K'' F.lieLat) (fun i => algebraMap K' K'' (x i)) n (-F.falt h / 2 - C)
        fun i σ => jetBd F.P₀.g (4 * n ^ 2) i (ρ (σ.comp (algebraMap K K'')))

theorem muGe_of_muLe {K : Type} [Field K] [NumberField K] {m : ℕ} {h : HermFam K (Fin m → K)}
    {E : Submodule (𝓞 K) (Fin m → K)} {ν : ℝ} (h₁ : MuLe h E ν) (h₂ : deg h E = m * ν)
    (h₃ : ∀ V : Submodule K (Fin m → K), latRank K (E ⊓ V.restrictScalars (𝓞 K)) = Module.finrank K V) : MuGe h E ν := by
  intro V
  have := h₁ (E ⊓ V.restrictScalars (𝓞 K)) inf_le_left
  rw [h₃] at this
  rw [h₂]
  linarith

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

variable {S : Scheme.{0}}

def ptMap {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    Over.mk (spMap φ ≫ s) ⟶ Over.mk s := Over.homMk (spMap φ)

@[simp] theorem ptMap_left {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    (ptMap s φ).left = spMap φ := rfl

abbrev dnInl (k : Type) [CommRing k] : k →+* DualNumber k := algebraMap k (DualNumber k)

abbrev dnFst (k : Type) [CommRing k] : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

structure Milnor {T T₁ T₂ T₀ : Scheme.{0}} (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂) : Prop where
  aff : IsAffine T
  aff₁ : IsAffine T₁
  aff₂ : IsAffine T₂
  closed : IsClosedImmersion k₂
  w : k₁ ≫ j₁ = k₂ ≫ j₂
  cart : IsPullback j₁.appTop j₂.appTop k₁.appTop k₂.appTop

variable (A : Over S) [GrpObj A] {U : Over S} (M : LB (A ⊗ U).left)

def FieldChart : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (T : Over S) (_ : T ⟶ Over.mk s) (N : LB (A ⊗ T).left),
    Fam A N → ChartAt A M N

def TanLift : Prop :=
  ∀ (k : Type) [Field k] (s : Sp k ⟶ S) (N : LB (A ⊗ Over.mk (spMap (dnInl k) ≫ s)).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ s) ⟶ U, Same A N M (ptMap _ (dnFst k)) u₀ →
      ∃ u : Over.mk (spMap (dnInl k) ≫ s) ⟶ U, Same A N M (𝟙 _) u

def SmallLift : Prop :=
  ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C →
    (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (Ideal.Quotient.mk (Ideal.span {e})) ≫ s) ⟶ U,
      Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) u₀ → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u

variable {A M}

theorem FieldChart.of_isChart (h : IsChart A M) : FieldChart A M := fun _ _ _ _ T _ N hN ↦ h.chart T N hN

theorem Milnor.id (T : Scheme.{0}) [IsAffine T] : Milnor (𝟙 T) (𝟙 T) (𝟙 T) (𝟙 T) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, rfl, by
    simpa using IsPullback.of_id_fst (f := 𝟙 Γ(T, ⊤))⟩

theorem Milnor.of_isPullback {R R₁ R₂ R₀ : CommRingCat.{0}} {a : R ⟶ R₁} {b : R ⟶ R₂} {c : R₁ ⟶ R₀} {d : R₂ ⟶ R₀}
    (h : IsPullback a b c d) (hd : Function.Surjective d) :
    Milnor (Spec.map a) (Spec.map b) (Spec.map c) (Spec.map d) where
  aff := inferInstance
  aff₁ := inferInstance
  aff₂ := inferInstance
  closed := IsClosedImmersion.spec_of_surjective d hd
  w := by rw [← Spec.map_comp, ← Spec.map_comp, h.w]
  cart := h.of_iso (Scheme.ΓSpecIso R).symm (Scheme.ΓSpecIso R₁).symm (Scheme.ΓSpecIso R₂).symm
    (Scheme.ΓSpecIso R₀).symm (by simp) (by simp) (by simp) (by simp)

theorem dnFst_surjective (k : Type) [CommRing k] : Function.Surjective (dnFst k) :=
  fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩

theorem dnFst_not_injective (k : Type) [CommRing k] [Nontrivial k] : ¬ Function.Injective (dnFst k) := fun h ↦ by
  have h1 : (DualNumber.eps : DualNumber k) = 0 := h (by rw [map_zero]; rfl)
  have h2 := congrArg TrivSqZeroExt.snd h1
  simp at h2

theorem Milnor.dualNumber (k : Type) [CommRing k] :
    Milnor (Spec.map (pullback.fst (CommRingCat.ofHom (dnFst k)) (CommRingCat.ofHom (dnFst k))))
      (Spec.map (pullback.snd (CommRingCat.ofHom (dnFst k)) (CommRingCat.ofHom (dnFst k))))
      (spMap (dnFst k)) (spMap (dnFst k)) :=
  Milnor.of_isPullback (IsPullback.of_hasPullback _ _) (dnFst_surjective k)

omit [GrpObj A] in

theorem lift_of_chartAt {C C' : Type} [CommRing C] [IsLocalRing C] [CommRing C'] [Nontrivial C'] (s : Sp C ⟶ S)
    (φ : C →+* C') (hφ : Function.Surjective φ) (N : LB (A ⊗ Over.mk s).left) (h : ChartAt A M N)
    (u₀ : Over.mk (spMap φ ≫ s) ⟶ U) (h₀ : Same A N M (ptMap s φ) u₀) :
    ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  obtain ⟨W, hW⟩ := h
  refine (hW _ (𝟙 _)).2 fun z ↦ ?_
  haveI : IsLocalRing C' := IsLocalRing.of_surjective' φ hφ
  haveI : IsLocalHom φ := IsLocalHom.of_surjective φ hφ
  have h1 := (hW _ (ptMap s φ)).1 ⟨u₀, h₀⟩ (IsLocalRing.closedPoint C')
  have h2 : IsLocalRing.closedPoint C ∈ (W : TopologicalSpace.Opens (PrimeSpectrum C)) := by
    rw [← IsLocalRing.comap_closedPoint φ]; exact h1
  have h3 := (IsLocalRing.closedPoint_mem_iff (R := C) W).1 h2
  rw [h3]; trivial

theorem TanLift.of_isChart (h : IsChart A M) : TanLift A M := fun k _ _ N hN u₀ h₀ ↦
  lift_of_chartAt _ (dnFst k) (dnFst_surjective k) N (h.chart _ N hN) u₀ h₀

theorem SmallLift.of_isChart (h : IsChart A M) : SmallLift A M := fun C _ _ e he _ s N hN u₀ h₀ ↦ by
  haveI : Nontrivial (C ⧸ Ideal.span {e}) := Ideal.Quotient.nontrivial_iff.2 (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact he)
  exact lift_of_chartAt s _ Ideal.Quotient.mk_surjective N (h.chart _ N hN) u₀ h₀

theorem not_isIso_spMap_dnFst (k : Type) [CommRing k] [Nontrivial k] : ¬ IsIso (spMap (dnFst k)) := by
  intro h
  have : IsIso (CommRingCat.ofHom (dnFst k)).op := by
    have : IsIso (Scheme.Spec.map (CommRingCat.ofHom (dnFst k)).op) := h
    exact isIso_of_reflects_iso _ Scheme.Spec
  have : IsIso (CommRingCat.ofHom (dnFst k)) := (isIso_op_iff _).1 this
  exact dnFst_not_injective k (ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (dnFst k))).1

theorem dnFst_comp_dnInl (k : Type) [CommRing k] : (dnFst k).comp (dnInl k) = RingHom.id k := by
  ext x; rfl

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.OfChar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField

namespace GlobalTheory.ThetaClauses

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure TupCl (R : RealDat D A Ks) : Prop where
  mu_off : R.tup_mu_off
  mu_used : R.tup_mu_used
  mu_ne : R.tup_mu_ne
  mu_conj : R.tup_mu_conj
  mu_on : R.tup_mu_on

structure CharTh (R : RealDat D A Ks) (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  thP : R.IsThP
  tup : TupCl R

end GlobalTheory.ThetaClauses
end

