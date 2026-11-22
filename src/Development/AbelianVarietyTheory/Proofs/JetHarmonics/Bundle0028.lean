import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermLinearPartCoordinatePointZero
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.GermDerivativeLinearMaps

section Calc

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_pderiv (f : PS k 1 d) (i : Fin d) :
    constantCoeff (pderiv k ((0 : Fin 1), i) f) = coeff (Finsupp.single ((0 : Fin 1), i) 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
  simp

theorem dLin_comp (φ ψ : Pt k 1 d) (hψ : GP ψ) : dLin (comp1 φ ψ) = dLin φ * dLin ψ := by
  ext i j
  refine (FormalCalc.coeff_single_subst (a := fun p : Fin 1 × Fin d => (![ψ] : Fin 1 → Pt k 1 d) p.1 p.2)
    (fun p => single_point_zero_constant hψ p.1 p.2) (φ i) _).trans ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.mul_apply]
  rfl

theorem germComp_matrixLinearMap_apply {n : ℕ} (U : Matrix (Fin d) (Fin d) k) (a : Pt k n d) (ha : GP a) (i : Fin d) :
    comp1 (LogExpAdaptedGauge.linMap U) a i = ∑ j, C (U i j) * a j := by
  have hz : FormalLog.CZ (![a] : Fin 1 → Pt k n d) := fun j l => single_point_zero_constant ha j l
  show ev ![a] (∑ j : Fin d, MvPowerSeries.C (U i j) * X ((0 : Fin 1), j)) = _
  rw [FormalLog.ev_sum hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FormalLog.ev_mul hz, FormalLog.ev_C hz, FormalLog.ev_X hz]
  rfl

theorem gp_linMap (U : Matrix (Fin d) (Fin d) k) : GP (LogExpAdaptedGauge.linMap U) := fun i => by
  simp [LogExpAdaptedGauge.linMap]

theorem dLin_linMap (U : Matrix (Fin d) (Fin d) k) : dLin (LogExpAdaptedGauge.linMap U) = U := by
  classical
  ext i j
  simp [dLin, LogExpAdaptedGauge.linMap, coeff_C_mul, coeff_X, Finsupp.single_left_inj]

theorem linMap_one {n : ℕ} (a : Pt k n d) (ha : GP a) : comp1 (LogExpAdaptedGauge.linMap (1 : Matrix (Fin d) (Fin d) k)) a = a := by
  classical
  funext i
  rw [germComp_matrixLinearMap_apply _ _ ha, Finset.sum_eq_single i] <;> simp +contextual [Matrix.one_apply, eq_comm]

end Calc

section Log

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

theorem additive_at {n : ℕ} (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (ψ : Pt k 1 d)
    (hψ : comp1 ψ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1))
    (a b : Pt k n d) (ha : GP a) (hb : GP b) : comp1 ψ (addOf F a b) = comp1 ψ a + comp1 ψ b := by
  have hV := pair_points_zero_constant ha hb
  have e := congrArg (evP ![a, b]) hψ
  have e2 : ∀ u v : Pt k 2 d, evP ![a, b] (u + v) = evP ![a, b] u + evP ![a, b] v := fun u v =>
    funext fun i => gt_ev_add _ hV _ _
  rw [e2, evP_comp1 _ hV _ _ (gp_addOf F hF _ _ (gp_pt 0) (gp_pt 1)),
    evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1), evP_comp1 _ hV _ _ (gp_pt 0),
    evP_comp1 _ hV _ _ (gp_pt 1), evP_pt _ hV, evP_pt _ hV] at e
  exact e

theorem germLinearPart_coordinatePoint_zero : dLin (pt k (n := 1) d 0) = 1 := by
  rw [← linMap_one (pt k (n := 1) d 0) (gp_pt 0), gt_comp1_pt_right, dLin_linMap]

theorem additive_eq_lin (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0) (ℓ ε ψ : Pt k 1 d)
    (h1 : dLin ℓ = 1) (hℓ : comp1 ℓ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1)) (hi : IsInvPair ℓ ε) (h0 : GP ψ)
    (hψ : comp1 ψ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1)) :
    ψ = comp1 (LogExpAdaptedGauge.linMap (dLin ψ)) ℓ := by
  classical
  have hε : GP ε := hi.2.1
  have hℓ0 : GP ℓ := hi.1
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 := gp_comp1 _ _ hε p0
  have q1 := gp_comp1 _ _ hε p1
  have ps : GP (pt k (n := 2) d 0 + pt k (n := 2) d 1) := fun i => by simp [pt]
  have e1 : comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      addOf F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) := by
    rw [← gt_comp_inv' hi _ (gp_addOf F hF _ _ q0 q1), additive_at F hF ℓ hℓ _ _ q0 q1,
      gt_comp_inv hi _ p0, gt_comp_inv hi _ p1]
  have e2 : comp1 (comp1 ψ ε) (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      comp1 (comp1 ψ ε) (pt k (n := 2) d 0) + comp1 (comp1 ψ ε) (pt k (n := 2) d 1) := by
    rw [gt_comp1_comp1 _ _ hε _ ps, gt_comp1_comp1 _ _ hε _ p0, gt_comp1_comp1 _ _ hε _ p1, e1,
      additive_at F hF ψ hψ _ _ q0 q1]
  have hdε : dLin ε = 1 := by
    have := dLin_comp ℓ ε hε
    rwa [hi.2.2.1, germLinearPart_coordinatePoint_zero, h1, one_mul, eq_comm] at this
  have e3 : comp1 ψ ε = LogExpAdaptedGauge.linMap (dLin ψ) := by
    have hd : dLin (comp1 ψ ε) = dLin (LogExpAdaptedGauge.linMap (dLin ψ)) := by
      rw [dLin_comp _ _ hε, hdε, mul_one, dLin_linMap]
    funext i
    ext e
    by_cases he : e.degree = 1
    · obtain ⟨⟨s, j⟩, rfl⟩ : ∃ s, e = Finsupp.single s 1 := by
        exact (Finsupp.sum_eq_one_iff e).1 he
      obtain rfl : s = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun hd i) j
    · rw [addition_linear k d _ (congrFun e2 i) e he]
      simp only [LogExpAdaptedGauge.linMap, map_sum, coeff_C_mul, coeff_X]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [if_neg, mul_zero]
      rintro rfl
      simp at he
  rw [← e3, gt_comp1_comp1 _ _ hε _ hℓ0, hi.2.2.2, gt_comp1_pt_right]

theorem exists_isLogExp {R : Type} [CommRing R] [Algebra R k] (G : FGLaw R d) :
    ∃ ℓ ε : Pt k 1 d, LogExpAdaptedGauge.IsLogExp k G ℓ ε := by
  obtain ⟨ℓ, h0, h1, h2⟩ := FormalLog.logSt k d (FBMap.mapLaw (algebraMap R k) G)
  obtain ⟨ε, hε⟩ := ChartInv.exists_isInvPair k d ℓ h0 (by rw [h1, Matrix.det_one]; exact isUnit_one)
  exact ⟨ℓ, ε, h1, h2, hε⟩

end Log

section Predicates

variable {C : Type} [NormedField C] [IsUltrametricDist C] {d : ℕ}

end Predicates

section Predicates2

variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
  {O : Type} [CommRing O] [StarRing O]

def comap {O' : Type} [CommRing O'] [StarRing O'] (f : O' →+* O) (hf : ∀ a, f (star a) = star (f a))
    (B : FB R d O) : FB R d O' :=
  { B with
    A :=
      { act := fun a => B.A.act (f a)
        const := fun a => B.A.const (f a)
        hom := fun a => B.A.hom (f a)
        add_act := fun a b => by rw [map_add, B.A.add_act]
        mul_act := fun a b => by rw [map_mul, B.A.mul_act]
        one_act := by rw [map_one, B.A.one_act] }
    ad := fun a => B.ad (f a)
    adjoint_zero_fst := fun a => B.adjoint_zero_fst (f a)
    adjoint_zero_snd := fun a => B.adjoint_zero_snd (f a)
    adjoint_compat_left := fun a => by simpa only [hf] using B.adjoint_compat_left (f a)
    adjoint_compat_right := fun a => by simpa only [hf] using B.adjoint_compat_right (f a)
    ad_one := by simpa only [map_one] using B.ad_one
    ad_mul := fun a b => by simpa only [hf, map_mul] using B.ad_mul (f a) (f b)
    ad_add := fun a b => by simpa only [hf, map_add] using B.ad_add (f a) (f b)
    ad_sy := fun a => by simpa only [hf] using B.ad_sy (f a) }

end Predicates2

section Letters

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

end Letters

section Frame

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

def ColumnBody (g : ℕ) (B : FB (LogExpAdaptedGauge.Ints C) d (𝓞 E)) (ε : Pt C 1 d) (h : PS C 2 d) (w0 : 𝓞 E)
    (u : PS (LogExpAdaptedGauge.Ints C) 2 d) : Prop :=
    ∀ n : ℕ, IsUnit (LogExpAdaptedGauge.colProd B u w0 n) ∧ ∃ hL : PS C n d, constantCoeff hL = 0 ∧
      FB.toK C (LogExpAdaptedGauge.colProd B u w0 n) * FB.expS C (LogExpAdaptedGauge.colSum C B h w0 n) = FB.expS C hL ∧
      ∀ (U : Matrix (Fin d) (Fin d) (LogExpAdaptedGauge.Ints C)) (ty : Fin d → (E →+* C)), LogExpAdaptedGauge.IsAdapted B U ty →
        LogExpAdaptedGauge.IntBelow g (LogExpAdaptedGauge.inChart (LogExpAdaptedGauge.letterChart ε U) hL) ∧
        ∀ m : Fin n × Fin d →₀ ℕ, coeff m (LogExpAdaptedGauge.inChart (LogExpAdaptedGauge.letterChart ε U) hL) ≠ 0 →
          3 ≤ LogExpAdaptedGauge.degTot m ∧
          ∃ (i : Fin n) (a b : Fin d), (∀ p, m p ≠ 0 → p.1 = i ∧ (ty p.2 = ty a ∨ ty p.2 = ty b)) ∧
            m (i, a) ≠ 0 ∧ m (i, b) ≠ 0 ∧ ty b = LogExpAdaptedGauge.conjType (ty a)

def ColumnFrameFor (g : ℕ) (B : FB (LogExpAdaptedGauge.Ints C) d (𝓞 E)) (ε : Pt C 1 d) (h : PS C 2 d) (w0 : 𝓞 E) : Prop :=
  ∃ u : PS (LogExpAdaptedGauge.Ints C) 2 d,
    ev (n := 1) ![0, pt (LogExpAdaptedGauge.Ints C) d 0] u = 1 ∧ ev (n := 1) ![pt (LogExpAdaptedGauge.Ints C) d 0, 0] u = 1 ∧
    ColumnBody g B ε h w0 u

def TwoPoint (B : FB (LogExpAdaptedGauge.Ints C) d (𝓞 E)) (ε : Pt C 1 d) (h : PS C 2 d) (u : PS (LogExpAdaptedGauge.Ints C) 2 d) : Prop :=
  ∃ h₂ : PS C 2 d, ev (n := 1) ![0, pt C d 0] h₂ = 0 ∧ ev (n := 1) ![pt C d 0, 0] h₂ = 0 ∧
    FB.toK C u * FB.expS C h = FB.expS C h₂ ∧
    ∀ (U : Matrix (Fin d) (Fin d) (LogExpAdaptedGauge.Ints C)) (ty : Fin d → (E →+* C)), LogExpAdaptedGauge.IsAdapted B U ty →
      bilinPart C (LogExpAdaptedGauge.inChart (LogExpAdaptedGauge.letterChart ε U) h₂) = 0 ∧
      ∀ m : Fin 2 × Fin d →₀ ℕ, coeff m (LogExpAdaptedGauge.inChart (LogExpAdaptedGauge.letterChart ε U) h₂) ≠ 0 →
        ∃ τ : E →+* C, (∀ i, m (0, i) ≠ 0 → ty i = τ) ∧ (∀ j, m (1, j) ≠ 0 → ty j = LogExpAdaptedGauge.conjType τ)

end Frame

def ColumnFrame : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → LogExpAdaptedGauge.SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (LogExpAdaptedGauge.Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), LogExpAdaptedGauge.IsLogExp C B.G ℓ ε →
  ∀ w0 : 𝓞 E, w0 + star w0 = 1 → ∃ h : PS C 2 d, LogExpAdaptedGauge.IsAdjGauge C B h ∧ ColumnFrameFor g B ε h w0

def UniformFrame : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → LogExpAdaptedGauge.SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (LogExpAdaptedGauge.Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), LogExpAdaptedGauge.IsLogExp C B.G ℓ ε →
  ∃ h : PS C 2 d, LogExpAdaptedGauge.IsAdjGauge C B h ∧ ∃ u : PS (LogExpAdaptedGauge.Ints C) 2 d,
    ev (n := 1) ![0, pt (LogExpAdaptedGauge.Ints C) d 0] u = 1 ∧ ev (n := 1) ![pt (LogExpAdaptedGauge.Ints C) d 0, 0] u = 1 ∧
    TwoPoint B ε h u ∧ ∀ w0 : 𝓞 E, w0 + star w0 = 1 → ColumnBody g B ε h w0 u

end GlobalTheory.GermDerivativeLinearMaps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantDerivAlongEndo
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.DerivEndo

open GlobalTheory.ChartTrans

variable {k : Type} [CommRing k] {d : ℕ}

theorem dof_endo (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (φ : Pt k 1 d) (hφ : GP φ)
    (hom : comp1 φ F = addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof F u (ev (n := 1) ![φ] g) = ev (n := 1) ![φ] (Dof F ((dLin φ).mulVec u) g) := by
  have h0 : GP (comp1 φ (pt k (n := 2) d 0)) := gp_comp1 φ _ hφ (gp_pt 0)
  have h1 : GP (comp1 φ (pt k (n := 2) d 1)) := gp_comp1 φ _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have key : ev (n := 2) ![F] (ev (n := 1) ![φ] g) =
      ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (ev (n := 2) ![F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF), vec1]
    have : evP ![F] φ = evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] F := hom
    rw [this]
  rw [dof_eq _ hF hu, dof_eq F hF hu, key, ChartTrans.ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp φ hφ, ChartTrans.ev_C_mul _ (single_point_zero_constant hφ)]
  simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dof_smul_dir (F : Fin d → PS k 2 d) (c : k) (u : Fin d → k) (g : PS k 1 d) :
    Dof F (c • u) g = C c * Dof F u g := by
  unfold Dof
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem iterate_dof_C_mul (F : Fin d → PS k 2 d) (u : Fin d → k) (n : ℕ) (c : k) (g : PS k 1 d) :
    (Dof F u)^[n] (C c * g) = C c * (Dof F u)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GE.dof_C_mul]

theorem dmonOf_endo (F : Fin d → PS k 2 d) (φ : Pt k 1 d) (hφ : GP φ) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (α : ι → k)
    (h : ∀ l g, Dof F (u l) (ev (n := 1) ![φ] g) = C (α l) * ev (n := 1) ![φ] (Dof F (u l) g))
    (m : ι →₀ ℕ) (g : PS k 1 d) :
    DmonOf F u m (ev (n := 1) ![φ] g) = C (∏ l, α l ^ m l) * ev (n := 1) ![φ] (DmonOf F u m g) := by
  have hit : ∀ (l : ι) (n : ℕ) (g : PS k 1 d), (Dof F (u l))^[n] (ev (n := 1) ![φ] g) =
      C (α l ^ n) * ev (n := 1) ![φ] ((Dof F (u l))^[n] g) := by
    intro l n g
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GE.dof_C_mul, h, pow_succ,
        map_mul, mul_assoc]
  rw [← Finset.prod_map_toList]
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, iterate_dof_C_mul, hit, List.map_cons, List.prod_cons,
      map_mul]
    ring

end GlobalTheory.DerivEndo

namespace GlobalTheory

open DerivEndo QuadDeriv

theorem invariantDeriv_along_endo : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (a : O), (∀ (u : Fin d → k) (g : PS k 1 d), Dof (B.FK k) u (ev (n := 1) ![B.actK k a] g) = ev (n := 1) ![B.actK k a] (Dof (B.FK k) ((dAct k B a).mulVec u) g)) ∧ ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → k) (α : ι → k), (∀ l, (dAct k B a).mulVec (u l) = α l • u l) → ∀ (m : ι →₀ ℕ) (g : PS k 1 d), constantCoeff (DmonOf (B.FK k) u m (ev (n := 1) ![B.actK k a] g)) = (∏ l, α l ^ m l) * constantCoeff (DmonOf (B.FK k) u m g) := by
  intro R _ d O _ _ k _ _ _ B a
  have hF : GP (B.FK k) := constantCoeff_mapP_eq_zero _ _ B.G.const
  have hw : GP (B.actK k a) := constantCoeff_mapP_eq_zero _ _ (B.A.const a)
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : comp1 (B.actK k a) (B.FK k) = addOf (B.FK k) (comp1 (B.actK k a) (pt k (n := 2) d 0))
      (comp1 (B.actK k a) (pt k (n := 2) d 1)) := by
    have := congrArg (mapP (algebraMap R k)) (B.A.hom a)
    rw [FGLaw.add, FGLaw.add, addOf_pt, baseChange_comp1 _ _ _ B.G.const,
      baseChange_addOf _ _ _ _ (gp_comp1 _ _ (B.A.const a) (gp_pt 0))
        (gp_comp1 _ _ (B.A.const a) (gp_pt 1)),
      baseChange_comp1 _ _ _ (gp_pt 0), baseChange_comp1 _ _ _ (gp_pt 1), baseChange_pt, baseChange_pt] at this
    exact this
  have h1 : ∀ (u : Fin d → k) (g : PS k 1 d), Dof (B.FK k) u (ev (n := 1) ![B.actK k a] g) =
      ev (n := 1) ![B.actK k a] (Dof (B.FK k) ((dAct k B a).mulVec u) g) :=
    dof_endo (B.FK k) hF (congrFun hU) (B.actK k a) hw hom
  refine ⟨h1, fun ι _ u α hα m g => ?_⟩
  rw [dmonOf_endo (B.FK k) (B.actK k a) hw u α (fun l g => by
    rw [h1, hα, dof_smul_dir, ChartTrans.ev_C_mul _ (single_point_zero_constant hw)]), map_mul, constantCoeff_C,
    constSt k d (B.actK k a) hw]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitFiniteHenselianOfLocal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory.AdicColimit

theorem smodEq_smul_top_map {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (J : Ideal A) (f : M →ₗ[A] N) {x y : M} (h : x ≡ y [SMOD (J • ⊤ : Submodule A M)]) :
    f x ≡ f y [SMOD (J • ⊤ : Submodule A N)] := by
  rw [SModEq.sub_mem] at h ⊢
  rw [← map_sub]
  have : (J • ⊤ : Submodule A M).map f ≤ J • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact this ⟨_, h, rfl⟩

theorem isAdicComplete_of_retract {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (J : Ideal A) (s : N →ₗ[A] M) (p : M →ₗ[A] N) (hps : ∀ x, p (s x) = x)
    (h : IsAdicComplete J M) : IsAdicComplete J N where
  haus' x hx := by
    have : s x = 0 := IsHausdorff.haus h.toIsHausdorff (s x) fun n => by
      simpa using smodEq_smul_top_map _ s (hx n)
    rw [← hps x, this, map_zero]
  prec' f hf := by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => s (f n)) fun {m n} hmn =>
      smodEq_smul_top_map _ s (hf hmn)
    exact ⟨p L, fun n => by simpa [hps] using smodEq_smul_top_map _ p (hL n)⟩

theorem isAdicComplete_map_eval {A ι : Type} [CommRing A] (T : ι → Type) [∀ i, CommRing (T i)]
    (e : A ≃+* Π i, T i) (J : Ideal A) (h : IsAdicComplete J A) (i : ι) :
    IsAdicComplete (J.map ((Pi.evalRingHom T i).comp e.toRingHom)) (T i) := by
  classical
  letI : Algebra A (T i) := ((Pi.evalRingHom T i).comp e.toRingHom).toAlgebra
  let s : T i →ₗ[A] A :=
    { toFun t := e.symm (Pi.single i t)
      map_add' x y := by rw [Pi.single_add, map_add]
      map_smul' a t := by
        apply e.injective
        rw [RingHom.id_apply, smul_eq_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply,
          ← Pi.single_mul_right]
        rfl }
  refine (IsAdicComplete.map_algebraMap_iff J (T i)).2
    (isAdicComplete_of_retract J s (Algebra.linearMap A (T i)) (fun t => ?_) h)
  change e (e.symm (Pi.single i t)) i = t
  rw [e.apply_symm_apply, Pi.single_eq_same]

theorem isAdicColimit_finite_henselian_of_local :
    (∀ (R : Type) [CommRing R] (I : Ideal R) (A : Type) [CommRing A] [IsLocalRing A] (φ : R →+* A), IsAdicComplete (I.map φ) A → IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ)))) → (∀ (R : Type) [CommRing R] (I : Ideal R) (T : Over (Spec (CommRingCat.of R))) (𝒰 : T.left.OpenCover.{0}), (∀ i j, i ≠ j → Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f j))) → (∀ i, IsAdicColimit I (Over.mk (𝒰.f i ≫ T.hom))) → IsAdicColimit I T) → ∀ (R : Type) [CommRing R] (I : Ideal R) (O : Type) [CommRing O] [HenselianLocalRing O] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] (φ : R →+* A), IsAdicComplete (I.map φ) A → IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  intro hloc hcov R _ I O _ _ A _ _ _ φ hc
  classical
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O A
  let π (i : ι) : A →+* T i := (Pi.evalRingHom T i).comp e.toRingEquiv.toRingHom
  have hopen (i : ι) : IsOpenImmersion (Spec.map (CommRingCat.ofHom (π i))) := by
    have : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) :=
      inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    infer_instance
  let 𝒰 : (Spec (CommRingCat.of A)).OpenCover := Scheme.Cover.mkOfCovers ι
    (fun i => Spec (CommRingCat.of (T i))) (fun i => Spec.map (CommRingCat.ofHom (π i))) (fun x => by
      obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
        (PrimeSpectrum.comap e.toRingEquiv.symm.toRingHom x)
      refine ⟨i, q, ?_⟩
      change PrimeSpectrum.comap e.toRingEquiv.toRingHom (PrimeSpectrum.comap (Pi.evalRingHom T i) q) = x
      rw [hq]
      ext a
      change e.symm (e a) ∈ x.asIdeal ↔ _
      rw [e.symm_apply_apply]) hopen
  refine hcov R I (Over.mk (Spec.map (CommRingCat.ofHom φ))) 𝒰 (fun i j hij => ?_) fun i => ?_
  · rw [Set.disjoint_left]
    rintro x ⟨p, rfl⟩ ⟨q, hq⟩
    change ι at i j
    change PrimeSpectrum (T i) at p
    change PrimeSpectrum (T j) at q
    change PrimeSpectrum.comap (π j) q = PrimeSpectrum.comap (π i) p at hq
    have h1 : e.symm (Pi.single i 1) ∈ (PrimeSpectrum.comap (π j) q).asIdeal := by
      change e (e.symm (Pi.single i 1)) j ∈ q.asIdeal
      rw [e.apply_symm_apply, Pi.single_eq_of_ne (i := i) (i' := j) (fun h => hij h.symm)]
      exact zero_mem _
    rw [hq] at h1
    change e (e.symm (Pi.single i 1)) i ∈ p.asIdeal at h1
    rw [e.apply_symm_apply, Pi.single_eq_same] at h1
    exact p.isPrime.one_notMem h1
  · change ι at i
    have := (hT i).1
    have key := hloc R I (T i) ((π i).comp φ) (by
      rw [← Ideal.map_map]
      exact isAdicComplete_map_eval T e.toRingEquiv _ hc i)
    rw [CommRingCat.ofHom_comp, Spec.map_comp] at key
    exact key

end GlobalTheory.AdicColimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory.FlatComplete

theorem mem_smul_top_iff_repr {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] [Fintype ι]
    (b : Module.Basis ι O M) (J : Ideal O) (x : M) :
    x ∈ J • (⊤ : Submodule O M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun y => ∀ i, b.repr y i ∈ J) hx ?_ ?_
    · intro r hr y _ i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · intro y z hy hz i
      rw [map_add, Finsupp.add_apply]
      exact J.add_mem (hy i) (hz i)
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isAdicComplete_of_finite_basis {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Fintype ι] (b : Module.Basis ι O M) (J : Ideal O) [hO : IsAdicComplete J O] :
    IsAdicComplete J M := by
  have hR : ∀ (n : ℕ) (r : O), r ∈ (J ^ n • ⊤ : Submodule O O) ↔ r ∈ J ^ n := fun n r => by
    rw [smul_eq_mul, Ideal.mul_top]
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (J ^ n • ⊤ : Submodule O M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (J ^ n • ⊤ : Submodule O O)] := fun n x y => by
    simp only [SModEq.sub_mem, hR, mem_smul_top_iff_repr b (J ^ n), map_sub, Finsupp.sub_apply]
  rw [isAdicComplete_iff]
  refine ⟨isHausdorff_iff.2 fun x hx => ?_, isPrecomplete_iff.2 fun f hf => ?_⟩
  · apply b.repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus (inferInstance : IsHausdorff J O) _ fun n => ?_
    have := (key n x 0).1 (hx n) i
    rwa [map_zero, Finsupp.zero_apply] at this
  · have hc : ∀ i, ∃ L : O, ∀ n, b.repr (f n) i ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)] := fun i =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete J O) fun hmn => (key _ _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    rw [← b.equivFun_apply (b.equivFun.symm L), LinearEquiv.apply_symm_apply]
    exact hL i n

theorem isAdicComplete_of_finite_flat (O : Type) [CommRing O] [IsLocalRing O] (J : Ideal O)
    (hO : IsAdicComplete J O) (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A]
    [Module.Flat O A] : IsAdicComplete (J.map (algebraMap O A)) A := by
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  have := hO
  exact (IsAdicComplete.map_algebraMap_iff (I := J) (M := A)).2
    (isAdicComplete_of_finite_basis (Module.Free.chooseBasis O A) J)

end GlobalTheory.FlatComplete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LowKSubSingleSqrtCkvLeStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowK_sub_single_sqrt_ckv_le : ∀ (n kk : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ) (s : Fin n), Shape ε kk μ bv → lowK ε (μ - Pi.single s 1) = lowK ε μ - Pi.single s 1 ∧ Real.sqrt (ckv ε (lowK ε μ)) + Real.sqrt n ≤ Real.sqrt (ckv ε (lowK ε (μ - Pi.single s 1))) + 8 * n := by
  first | exact @GlobalTheory.lowK_sub_single_and_sqrt_ckv_le | exact GlobalTheory.lowK_sub_single_and_sqrt_ckv_le | (intros; apply GlobalTheory.lowK_sub_single_and_sqrt_ckv_le <;> assumption)
end

