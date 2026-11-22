import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0110
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0127
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.FormalDegreeBessel.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdPartialZpow
section
open Matrix Finset Formalism.MainNotions.S GlobalTheory.Dec

namespace GlobalTheory.PhiTriangular

theorem sum_sInt_from {n : ℕ} (lam : Fin n → ℝ) (l : Fin n) :
    ∑ i : Fin n, (if l ≤ i then sInt lam i else 0) = muInt lam l := by
  let m : ℕ → ℤ := fun k => if h : k < n then muInt lam ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin n, (if l ≤ i then sInt lam i else 0) =
      m (max i.val l.val) - m (max (i.val + 1) l.val) := by
    intro i
    by_cases h : l ≤ i
    · have h' : l.val ≤ i.val := h
      rw [if_pos h, max_eq_left h', max_eq_left (by omega : l.val ≤ i.val + 1)]
      simp only [m, sInt, dif_pos i.isLt]
    · have h' : i.val < l.val := by simpa using h
      rw [if_neg h, max_eq_right h'.le, max_eq_right (by omega : i.val + 1 ≤ l.val), sub_self]
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => m (max k l.val) - m (max (k + 1) l.val)) n,
    Finset.sum_range_sub' (fun k => m (max k l.val)) n, max_eq_right (Nat.zero_le _),
    max_eq_left l.isLt.le]
  simp [m]

theorem prod_castLE_succ {n : ℕ} (d : Fin n → ℂ) (i : Fin n) :
    ∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j) = ∏ l : Fin n, if l ≤ i then d l else 1 := by
  refine Finset.prod_of_injOn (Fin.castLE i.isLt) ((Fin.castLE_injective _).injOn) (by simp) ?_ ?_
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk ⟨⟨k.val, Nat.lt_succ_of_le h⟩, by simp, rfl⟩
  · intro j _
    rw [if_pos]
    exact Nat.le_of_lt_succ j.isLt

theorem zpow_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℤ) {a : ℂ} (ha : a ≠ 0) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

theorem prod_partial_zpow {n : ℕ} (lam : Fin n → ℝ) (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) :
    ∏ i : Fin n, (∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j)) ^ (-(sInt lam i)) =
      ∏ l, d l ^ (-(muInt lam l)) := by
  simp only [prod_castLE_succ, ← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← sum_sInt_from, ← Finset.sum_neg_distrib, zpow_finset_sum _ _ (hd l)]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : l ≤ i <;> simp [h]

theorem phiTri : PhiTri := by
  intro n lam c z c' hc hc' hd hz
  have hd' : ∀ l, c l l * c' l l ≠ 0 := fun l => mul_ne_zero (hd l).1 (hd l).2
  refine ⟨fun i => ?_, ?_⟩
  · rw [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc']
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hd' _) (hz i)
  · unfold Phi
    simp only [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc', mul_zpow _ (leadMinor z _ _)]
    rw [Finset.prod_mul_distrib, prod_partial_zpow lam (fun l => c l l * c' l l) hd']

end GlobalTheory.PhiTriangular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentRadicalMemAdelic
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Proof.rational_unipotentRadical_mem_adelic

theorem sub_one_map {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) E) : g.map ι - 1 = (g - 1).map ι := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_mulVec_incl {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    M.map ι *ᵥ (fun i => ι (w i)) = fun i => ι ((M *ᵥ w) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem map_mulVec_span {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E)) (T : Submodule A (Fin n → A))
    (h : ∀ w ∈ S, (fun i => ι ((M *ᵥ w) i)) ∈ T) :
    ∀ y ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S), M.map ι *ᵥ y ∈ T := by
  intro y hy
  have : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S) ≤
      T.comap (M.map ι).mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    rw [map_mulVec_incl]
    exact h w hw
  exact this hy

theorem span_univ {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ} :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' Set.univ) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun A (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  apply Submodule.subset_span
  refine ⟨Pi.single j 1, trivial, ?_⟩
  funext i
  by_cases h : i = j <;> simp [Pi.single_apply, h]

theorem inUnipRad_map (I : AutInst) {A : Type} [CommRing A] (σ : I.E →+* I.E) (s : A →+* A)
    (ι : I.E →+* A) (hι : ∀ e, s (ι e) = ι (σ e)) (W : Submodule I.E (Fin I.n → I.E))
    (g : Matrix (Fin I.n) (Fin I.n) I.E) (hg : I.InUnipRad σ I.J W g) :
    I.InUnipRad s (I.J.map ι)
      (Submodule.span A ((fun w : Fin I.n → I.E => fun i => ι (w i)) '' (W : Set _))) (g.map ι) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hp := GlobalTheory.PerpBaseChange.perpSet_baseChange I.E A σ s ι I.n I.J W hι
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [sub_one_map]
    have h0 : ∀ w ∈ (W : Set (Fin I.n → I.E)), (fun i => ι (((g - 1) *ᵥ w) i)) ∈ (⊥ : Submodule A (Fin I.n → A)) := by
      intro w hw
      rw [h1 w hw, Submodule.mem_bot]
      funext i
      exact map_zero ι
    have := map_mulVec_span ι (g - 1) (W : Set (Fin I.n → I.E)) ⊥ h0 x hx
    exact (Submodule.mem_bot A).1 this
  · intro y hy
    replace hy := (Set.ext_iff.1 hp y).1 hy
    rw [sub_one_map]
    refine map_mulVec_span ι (g - 1) _ _ (fun w hw => ?_) y hy
    exact Submodule.subset_span ⟨_, h2 w hw, rfl⟩
  · intro y
    refine (Set.ext_iff.1 hp _).2 ?_
    rw [sub_one_map]
    refine map_mulVec_span ι (g - 1) Set.univ _ (fun w _ => ?_) y (by rw [span_univ]; trivial)
    exact Submodule.subset_span ⟨_, h3 w, rfl⟩

theorem unitary_map {E A : Type} [CommRing E] [CommRing A] (σ : E →+* E) (s : A →+* A)
    (ι : E →+* A) (hι : ∀ e, s (ι e) = ι (σ e)) {n : ℕ} (J g : Matrix (Fin n) (Fin n) E)
    (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT s (g.map ι) * J.map ι * g.map ι = J.map ι := by
  have : Formalism.UG.cT s (g.map ι) = (Formalism.UG.cT σ g).map ι := by
    ext i j
    simp [Formalism.UG.cT, hι]
  rw [this, ← Matrix.map_mul, ← Matrix.map_mul, hg]

theorem rational_mem_adelic (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (hN : I.InUnipRad (starRingEnd I.E) I.J W (γ : Matrix (Fin I.n) (Fin I.n) I.E)) :
    ∃ a ∈ I.GFset ∩ I.NA W,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hφ : ∀ v e, starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e) :=
    fun v e => (I.cm.cmUnram.2.1 (I.φ v) e).symm
  have hf : ∀ e, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) := by
    intro e
    simp [Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  have hdet : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPP : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v => Matrix.mul_nonsing_inv _ (hdet v)
  let u : ∀ v : InfinitePlace I.F, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Formalism.UG.bc (I.φ v) γ * (I.P_unit v).unit
  have hu : ∀ v, (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [u, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hPu : ∀ v, I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    rw [hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hU : ∀ v, u v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    change (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * Jm (I.ε v) * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) = Jm (I.ε v)
    have h := unitary_map _ _ (I.φ v) (hφ v) I.J _ hγ
    have hc : Formalism.UG.cT (starRingEnd ℂ) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) =
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ := by
      ext i j
      simp [Formalism.UG.cT]
    rw [hc] at h
    rw [← I.P_spec v]
    calc (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) *
          (u v : Matrix (Fin I.n) (Fin I.n) ℂ)
        = (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ))ᴴ * I.J.map (I.φ v) *
          (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (I.P v)ᴴ * (((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
          (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by
          rw [hPu]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h]
  have hF : Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) γ ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    unitary_map _ _ _ hf I.J _ hγ
  refine ⟨(fun v => ⟨u v, hU v⟩, ⟨_, hF⟩), ⟨⟨γ, hγ, hu, rfl⟩, fun v => ?_, ?_⟩, hu, rfl⟩
  · change I.InUnipRad _ _ _ (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) * (I.P v)⁻¹)
    rw [hPu, Matrix.mul_assoc, hPP, Matrix.mul_one]
    exact inUnipRad_map I _ _ _ (hφ v) W _ hN
  · exact inUnipRad_map I _ _ _ hf W _ hN

end GlobalTheory.Proof.rational_unipotentRadical_mem_adelic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentRadicalEmbedsAdelicRadical
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RadEmb

theorem hform_eq_dot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) A x y = star x ⬝ᵥ (A *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_frame {n : ℕ} {ε : Fin n → Bool} {A P : Matrix (Fin n) (Fin n) ℂ} (h : Pᴴ * A * P = Jm ε)
    (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) A (P *ᵥ x) (P *ᵥ y) = star (Formalism.QuantumDeterminants.herm (Jm ε) x y) := by
  have e : star x ⬝ᵥ (Jm ε *ᵥ y) = star (Formalism.QuantumDeterminants.herm (Jm ε) x y) := by
    simp only [Formalism.QuantumDeterminants.herm, Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [mul_comm]
  rw [← e, ← h, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

theorem inUnipRad_one (I : AutInst) {A : Type} [CommRing A] (s : A →+* A) (JA : Matrix (Fin I.n) (Fin I.n) A)
    (WA : Submodule A (Fin I.n → A)) : I.InUnipRad s JA WA 1 := by
  refine ⟨fun x _ => by simp, fun y _ => by simp, fun y x _ => by simp [Formalism.UG.hform]⟩

theorem span_isot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F) (hW : I.IsIsot W) :
    ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
    ∀ y ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x y = 0 := by
  have hφ : ∀ a, I.φ v (starRingEnd I.E a) = starRingEnd ℂ (I.φ v a) := fun a => I.cm.cmUnram.2.1 _ a
  intro x hx y hy
  rw [hform_eq_dot]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have := congrArg (I.φ v) (hW.2 a ha b hb)
      rw [← hform_eq_dot]
      simpa only [Formalism.UG.hform, map_sum, map_mul, hφ, map_zero, Matrix.map_apply] using this
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add, dotProduct_add, ha, hb, add_zero]
    | smul c a _ ha => rw [Matrix.mulVec_smul, dotProduct_smul, ha, smul_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
  | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]

theorem radical_embeds : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F), I.IsIsot W →
    ∃ Wv : Submodule ℂ (Fin I.n → ℂ), IsIsoC (I.ε v) Wv ∧
      ∀ m ∈ NW (I.ε v) Wv, (open Classical in ((Pi.mulSingle v m, 1) : I.GA)) ∈ I.NA W := by
  classical
  intro I W v hW
  have hP : ∀ u, I.P u * (I.P u)⁻¹ = 1 := fun u =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit u))
  have hQ : ∀ y, I.P v *ᵥ ((I.P v)⁻¹ *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  set WA := Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)) with hWA
  have hf := hform_frame (I.P_spec v)
  refine ⟨WA.comap (I.P v).mulVecLin, ⟨?_, fun x hx y hy => ?_⟩, fun m hm => ⟨fun u => ?_, ?_⟩⟩
  · intro h
    apply hW.1
    rw [eq_bot_iff]
    intro w hw
    have h1 : (I.P v)⁻¹ *ᵥ (fun i => I.φ v (w i)) ∈ WA.comap (I.P v).mulVecLin := by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hQ]
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    have h2 := hQ (fun i => I.φ v (w i))
    rw [h1, Matrix.mulVec_zero] at h2
    rw [Submodule.mem_bot]
    funext i
    exact (map_eq_zero (I.φ v)).1 (congrFun h2 i).symm
  · have := span_isot I W v hW _ hx _ hy
    simp only [Matrix.mulVecLin_apply] at this
    rw [hf] at this
    exact star_eq_zero.1 this
  · by_cases hu : u = v
    · subst hu
      simp only [Pi.mulSingle_eq_same]
      have e : ∀ y, (I.P u * uMat m * (I.P u)⁻¹ - 1) *ᵥ y = I.P u *ᵥ ((umat m - 1) *ᵥ ((I.P u)⁻¹ *ᵥ y)) := by
        intro y
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP]
      have mem : ∀ x ∈ WA, (I.P u)⁻¹ *ᵥ x ∈ WA.comap (I.P u).mulVecLin := fun x hx => by
        rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hQ]; exact hx
      refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩
      · rw [e, hm.1 _ (mem x hx), Matrix.mulVec_zero]
      · rw [e]
        refine hm.2.1 _ fun x hx => ?_
        have := hy _ hx
        rw [← hQ y, Matrix.mulVecLin_apply, hf] at this
        exact star_eq_zero.1 this
      · rw [e, ← hQ x, hf, hm.2.2 _ _ (mem x hx), star_zero]
    · have e : uMat ((Pi.mulSingle v m : I.Ginf) u) = 1 := by
        rw [Pi.mulSingle_eq_of_ne hu]; rfl
      simp only [e, Matrix.mul_one, hP]
      exact inUnipRad_one I _ _ _
  · exact inUnipRad_one I _ _ _

end GlobalTheory.RadEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCoset
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.Amp.RootMove

variable {k r : ℕ}

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
theorem _root_.GlobalTheory.Amp.RootMove.det_Hpk : IsUnit (_root_.Formalism.QuantumDeterminants.Hpk k r).det := by
  refine isUnit_iff_exists_inv.2 ⟨(_root_.Formalism.QuantumDeterminants.Hpk k r).det, ?_⟩
  rw [← Matrix.det_mul, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
theorem _root_.GlobalTheory.Amp.RootMove.unit_det {g : _root_.Formalism.MainNotions.S.MatKR k r} (hg : g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) :
    IsUnit g.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg

def lr (a b : MatKR k r) : Mt k r → Mt k r := fun x => fun i j => (a * Matrix.of x * b) i j

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
theorem _root_.GlobalTheory.Amp.RootMove.continuous_lr (a b : _root_.Formalism.MainNotions.S.MatKR k r) :
    Continuous (_root_.GlobalTheory.Amp.RootMove.lr a b) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [_root_.GlobalTheory.Amp.RootMove.lr, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
private theorem isClosed_Nset' : IsClosed (_root_.Formalism.QuantumDeterminants.Nset k r) := by
  have hent : ∀ i j, Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => g i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have e : _root_.Formalism.QuantumDeterminants.Nset k r = {g | gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r} ∩
      ((⋂ (a : Fin r) (i : Fin (2 * r + k + 1)) (_ : (a : ℕ) ≤ i),
        {g | g i (_root_.Formalism.QuantumDeterminants.eI k r a) = if i = _root_.Formalism.QuantumDeterminants.eI k r a then 1 else 0}) ∩
      ⋂ (i : Fin (2 * r + k + 1)) (j : Fin (2 * r + k + 1)) (_ : r ≤ (j : ℕ)) (_ : (j : ℕ) ≤ r + k)
        (_ : r ≤ (i : ℕ)), {g | g i j = if i = j then 1 else 0}) := by
    ext g
    simp only [_root_.Formalism.QuantumDeterminants.Nset, _root_.Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const) (IsClosed.inter ?_ ?_)
  · exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (hent _ _) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (hent _ _) continuous_const

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
theorem _root_.GlobalTheory.Amp.RootMove.measurableSet_notR (g : _root_.Formalism.MainNotions.S.MatKR k r) :
    MeasurableSet {x : _root_.Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ _root_.Formalism.MainNotions.S.Rset k r g} := by
  have h1 : Continuous fun x : _root_.Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := continuous_id
  have h2 : Continuous fun x : _root_.Formalism.QuantumDeterminants.Mt k r =>
      (g * Matrix.of x * g⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    (continuous_const.matrix_mul h1).matrix_mul continuous_const
  have hc : IsClosed {x : _root_.Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ _root_.Formalism.MainNotions.S.Rset k r g} :=
    (isClosed_Nset'.preimage h1).inter (isClosed_Nset'.preimage h2)
  exact hc.measurableSet.compl

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
theorem _root_.GlobalTheory.Amp.RootMove.measurable_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : _root_.Formalism.MainNotions.S.Point ℂ (r + 1)) :
    Measurable (_root_.Formalism.MainNotions.S.rootCoords k r z p) := by
  refine measurable_pi_lambda _ fun q => Continuous.measurable ?_
  by_cases hi : ((q : Fin (r + 1) × Fin (r + 1)).1 : ℕ) < r
  · simp only [_root_.Formalism.MainNotions.S.rootCoords, _root_.Formalism.MainNotions.S.flagMat, hi, dite_true, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  · simp only [_root_.Formalism.MainNotions.S.rootCoords, _root_.Formalism.MainNotions.S.flagMat, hi, dite_false]
    exact continuous_const

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
private theorem flagMat_conj_eq_of_mem_UWset {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z)
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    _root_.Formalism.MainNotions.S.flagMat k r z (h * X * h⁻¹) = _root_.Formalism.MainNotions.S.flagMat k r z X := by
  have hfix : ∀ {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}, g ∈ _root_.Formalism.QuantumDeterminants.UWset k r z →
      ∀ c, g *ᵥ _root_.Formalism.QuantumDeterminants.fvec k r z c = _root_.Formalism.QuantumDeterminants.fvec k r z c := by
    intro g hg c
    obtain ⟨-, hb, hz⟩ := hg
    unfold _root_.Formalism.QuantumDeterminants.fvec
    split_ifs with hc
    · exact (hb _).1
    · exact hz
  obtain ⟨hU, hb, -⟩ := id hh
  have hrow : ∀ (a : Fin r) (j : Fin (2 * r + k + 1)),
      h (_root_.Formalism.QuantumDeterminants.eI k r a) j = if _root_.Formalism.QuantumDeterminants.eI k r a = j then 1 else 0 := by
    intro a j
    have hτ : _root_.Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (_root_.Formalism.QuantumDeterminants.esI k r a) = _root_.Formalism.QuantumDeterminants.eI k r a := by
      have := a.isLt
      ext
      simp only [_root_.Formalism.QuantumDeterminants.WeylGroupFacts.tau, _root_.Formalism.QuantumDeterminants.esI, _root_.Formalism.QuantumDeterminants.eI]
      by_cases hc : 2 * r + k - (a : ℕ) < r ∨ r + k < 2 * r + k - (a : ℕ)
      · simp only [hc, ↓reduceIte]; omega
      · omega
    rw [← hτ]
    exact _root_.Formalism.QuantumDeterminants.WeylGroupFacts.row_of_fixed_col hU _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.col_of_fix (hb a).2) j
  ext i j
  simp only [_root_.Formalism.MainNotions.S.flagMat, Matrix.of_apply]
  split_ifs with hi
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh), _root_.Formalism.QuantumDeterminants.WeylGroupFacts.mulVec_apply_of_row _ _ (hrow _)]
  all_goals rfl

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in

theorem _root_.GlobalTheory.Amp.RootMove.rootMeas_move : ∀ (D : _root_.Formalism.BasicNotions.D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (p : _root_.Formalism.MainNotions.S.Point ℂ (D.R.rS + 1)) (g a a' : _root_.Formalism.MainNotions.S.MatKR D.R.k D.R.rS) (μ : Measure (_root_.Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)), _root_.Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z → _root_.Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z' → 0 < _root_.Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z → 0 < _root_.Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z' → g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) → a ∈ _root_.Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z → a' ∈ _root_.Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z' → _root_.Formalism.MainNotions.S.IsRootMeasR D z z' p g μ → _root_.Formalism.MainNotions.S.IsRootMeasR D z z' p (a * g * a'⁻¹) (μ.map fun x => fun i j => (a' * Matrix.of x * a'⁻¹) i j) := by
  intro D z z' p g a a' μ hz hz' _ _ _ ha ha' hμ
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  obtain ⟨h', hh', m', hm', rfl⟩ := ha'
  obtain ⟨n, hn, n', hn', g₀, rfl, hZ, μ₀, hnull, hmap, rfl⟩ := hμ
  have hd : IsUnit h.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have hd' : IsUnit h'.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh'.1
  have hdm' : IsUnit m'.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ((_root_.Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff m').1 hm').1
  have hc' : Continuous (_root_.GlobalTheory.Amp.RootMove.lr h' h'⁻¹) :=
    _root_.GlobalTheory.Amp.RootMove.continuous_lr h' h'⁻¹
  refine ⟨h * (m * n) * h⁻¹, (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z hz h hh _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hm hn)).1,
    h' * (n' * m'⁻¹) * h'⁻¹, (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z' hz' h' hh' _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hn' (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hm'))).1,
    h * g₀ * h'⁻¹, ?_, ?_, μ₀.map (_root_.GlobalTheory.Amp.RootMove.lr h' h'⁻¹), ?_, ?_, ?_⟩
  · rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
      Matrix.nonsing_inv_mul_cancel_left _ _ hd']
  · have hF : h⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z = _root_.Formalism.QuantumDeterminants.Fm _ _ z := _root_.Formalism.QuantumDeterminants.UW_F (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh)
    have hF' : h'⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z' = _root_.Formalism.QuantumDeterminants.Fm _ _ z' := _root_.Formalism.QuantumDeterminants.UW_F (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh')
    have hU : (h⁻¹)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hh.1
    have hU2 : (h⁻¹)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h := by
      conv_rhs => rw [← hU]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    have key : (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h = (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
      rw [Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hF]
    have E : (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (h * g₀ * h'⁻¹) * _root_.Formalism.QuantumDeterminants.Fm _ _ z' =
        (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * g₀ * _root_.Formalism.QuantumDeterminants.Fm _ _ z' := by
      calc _ = ((_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h) * g₀ * (h'⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z') := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [key, hF']
    rw [← hZ]
    unfold _root_.Formalism.MainNotions.S.ZhatO
    rw [_root_.Formalism.QuantumDeterminants.Zhat_eq, _root_.Formalism.QuantumDeterminants.Zhat_eq, E]
  · rw [Measure.map_apply hc'.measurable (_root_.GlobalTheory.Amp.RootMove.measurableSet_notR _)]
    refine measure_mono_null ?_ hnull
    intro x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    intro hR
    apply hx
    obtain ⟨hR1, hR2⟩ := hR
    have e : (h * g₀ * h'⁻¹) * (h' * Matrix.of x * h'⁻¹) * (h * g₀ * h'⁻¹)⁻¹ =
        h * (g₀ * Matrix.of x * g₀⁻¹) * h⁻¹ := by
      simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd', Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ hd']
    refine ⟨(_root_.Formalism.QuantumDeterminants.uWNormal _ _ z' hz' h' hh' _ hR1).1, ?_⟩
    change (h * g₀ * h'⁻¹) * (h' * Matrix.of x * h'⁻¹) * (h * g₀ * h'⁻¹)⁻¹ ∈ _
    rw [e]
    exact (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z hz h hh _ hR2).1
  · rw [Measure.map_map (_root_.GlobalTheory.Amp.RootMove.measurable_rootCoords z' p) hc'.measurable]
    convert hmap using 2
    funext x
    have hx := flagMat_conj_eq_of_mem_UWset hh' (Matrix.of x)
    simp only [Function.comp_apply]
    unfold _root_.Formalism.MainNotions.S.rootCoords
    exact congrArg (fun M => fun q : ↥(_root_.Formalism.MainNotions.S.rootPat p) => M q.1.1 q.1.2) hx
  · have E : ∀ X : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
        (h' * m') * (n'⁻¹ * X * n') * (h' * m')⁻¹ =
          (h' * (n' * m'⁻¹) * h'⁻¹)⁻¹ * (h' * X * h'⁻¹) * (h' * (n' * m'⁻¹) * h'⁻¹) := by
      intro X
      simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd',
        Matrix.nonsing_inv_nonsing_inv _ hdm', Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ hd']
    rw [Measure.map_map, Measure.map_map]
    · congr 1
      funext x i j
      exact congrArg (fun M : Matrix _ _ ℂ => M i j) (E (Matrix.of x))
    all_goals exact (_root_.GlobalTheory.Amp.RootMove.continuous_lr _ _).measurable

end GlobalTheory.Amp.RootMove
end
end

