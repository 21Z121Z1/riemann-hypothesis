import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ContinuousPA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.Bundle0002
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PairZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ProperRatH
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Bundle0001

-- bundled from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CuspPairA
section
set_option linter.all false

noncomputable section

open NumberField Matrix
open GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic
  GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.BcB PositivityTheory.Rg.Rs.JInitBnd

namespace DiscreteGroups.T1.G.CP

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]; constructor <;> linarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b]

theorem abs_add_le_abs_add_abs (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rw [abs_le]; constructor <;> linarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b]

theorem lAbs_mul (x y : GA E n) : logAbs (x * y).val.det = logAbs x.val.det + logAbs y.val.det := by
  rw [Units.val_mul, Matrix.det_mul]
  exact (D1.logAbsBasic E).2.1 _ _ (Matrix.isUnits_det_units x) (Matrix.isUnits_det_units y)

theorem lAbs_rat (γ : GL (Fin n) E) : logAbs (ratGL E n γ).val.det = 0 := by
  have h : (ratGL E n γ).val.det = algebraMap E (Ad E) γ.val.det := by
    rw [RingHom.map_det]; rfl
  rw [h]
  exact (D1.logAbsBasic E).2.2 _ (Matrix.isUnits_det_units γ).ne_zero

theorem lAbs_one : logAbs (1 : GA E n).val.det = 0 := by
  have h := lAbs_mul (E := E) (n := n) 1 1
  rw [mul_one] at h
  linarith

theorem lAbs_pow (k : GA E n) (m : ℕ) : logAbs (k ^ m).val.det = m * logAbs k.val.det := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact lAbs_one
  | succ m ih => rw [pow_succ, lAbs_mul, ih]; push_cast; ring

theorem eq_zero_of_nat_mul_le {a C : ℝ} (h : ∀ m : ℕ, (m : ℝ) * |a| ≤ C) : a = 0 := by
  by_contra ha
  have hpos : 0 < |a| := abs_pos.2 ha
  obtain ⟨m, hm⟩ := exists_nat_gt (C / |a|)
  have h1 := h m
  have h2 : C / |a| * |a| < m * |a| := mul_lt_mul_of_pos_right hm hpos
  rw [div_mul_cancel₀ _ hpos.ne'] at h2
  linarith

theorem lAbs_maxCompact {k : GA E n} (hk : k ∈ maxCompact (K := E) (n := n)) : logAbs k.val.det = 0 := by
  obtain ⟨C, hC⟩ := (isCompact_maxCompact (K := E) (n := n)).exists_bound_of_continuousOn
    (DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)).continuousOn
  refine eq_zero_of_nat_mul_le (C := C) fun m => ?_
  have h := hC (k ^ m) (pow_mem hk m)
  rw [Real.norm_eq_abs, lAbs_pow, abs_mul, Nat.abs_cast] at h
  exact h

theorem lAbs_posIdele (ρ : ℝ) (hρ : 0 < ρ) :
    logAbs ((posIdele (K := E) ρ hρ : (Ad E)ˣ) : Ad E) = Module.finrank ℚ E * Real.log ρ := by
  rw [GlobalTheory.CuspBoundSiegel.posIdele_congr hρ (Real.exp_pos (Real.log ρ)) (Real.exp_log hρ).symm,
    PositivityTheory.Rg.BcB.E1.posIdele_val, PositivityTheory.Rg.BcB.E1.logAbs_pA]

theorem lAbs_prod (s : Finset (Fin n)) (u : Fin n → (Ad E)ˣ) :
    logAbs (∏ i ∈ s, (u i : Ad E)) = ∑ i ∈ s, logAbs (u i : Ad E) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty]
    have h := (D1.logAbsBasic E).2.2 (1 : E) one_ne_zero
    rwa [map_one] at h
  · intro a s ha ih
    have hu : IsUnit (∏ i ∈ s, (u i : Ad E)) := by rw [← Units.coe_prod]; exact Units.isUnit _
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (D1.logAbsBasic E).2.1 _ _ (u a).isUnit hu, ih]

theorem lAbs_diag (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    logAbs (diagUnits n (fun i => posIdele (K := E) (r i) (hr i))).val.det =
      Module.finrank ℚ E * ∑ i, Real.log (r i) := by
  rw [coe_diagUnits, Matrix.det_diagonal]
  refine (lAbs_prod Finset.univ fun i => (posIdele (K := E) (r i) (hr i) : (Ad E)ˣ)).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => lAbs_posIdele (r i) (hr i)

theorem sum_sr (ℓ : Fin n → ℝ) (hn : 0 < n) :
    ∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ r = ℓ ⟨0, hn⟩ - ℓ ⟨n - 1, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have h0 : PositivityTheory.Rg.Rs.An.sr ℓ 0 = 0 := by simp [PositivityTheory.Rg.Rs.An.sr]
  rw [h0, add_zero]
  have h1 : ∀ k ∈ Finset.range m, PositivityTheory.Rg.Rs.An.sr ℓ (k + 1) = ext0 ℓ k - ext0 ℓ (k + 1) := fun k hk => by
    rw [Finset.mem_range] at hk
    rw [sr_eq ℓ (by omega) (by omega), Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl h1, Finset.sum_range_sub']
  rw [ext0, ext0, dif_pos (by omega), dif_pos (by omega)]
  rfl

theorem coord_bound (ℓ : Fin n → ℝ) (hn : 0 < n) (t₀ S : ℝ) (ht : ∀ r, -t₀ ≤ PositivityTheory.Rg.Rs.An.sr ℓ r)
    (hS : |∑ i, ℓ i| ≤ S) (i : Fin n) :
    |ℓ i| ≤ S + 2 * (∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ r + 2 * (n : ℝ) * t₀) := by
  have hc0 : n - 1 < n := by omega
  set c := ℓ ⟨n - 1, hc0⟩ with hcdef
  set x' : Fin n → ℝ := fun j => ℓ j - c with hx'
  have hsr : ∀ r, PositivityTheory.Rg.Rs.An.sr x' r = PositivityTheory.Rg.Rs.An.sr ℓ r := fun r => by
    unfold PositivityTheory.Rg.Rs.An.sr; split_ifs <;> simp [hx']
  have hx'' : ∀ r, -t₀ ≤ PositivityTheory.Rg.Rs.An.sr x' r := fun r => (hsr r).symm ▸ ht r
  have hlast : ∀ j : Fin n, (j : ℕ) + 1 = n → x' j = 0 := fun j hj => by
    have hj' : j = ⟨n - 1, hc0⟩ := Fin.ext (by simp only; omega)
    simp only [hx', hcdef, hj', sub_self]
  have hS' : ∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr x' r = ∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ r :=
    Finset.sum_congr rfl fun r _ => hsr r
  set B := ∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ r + 2 * (n : ℝ) * t₀ with hB
  have hB0 : 0 ≤ B := bound_nonneg ℓ t₀ ht
  have hb : ∀ j, |ℓ j - c| ≤ B := fun j => by
    have h := abs_le_bound x' t₀ hx'' hlast j
    rw [hS'] at h
    exact h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hS
  have e : (n : ℝ) * c = ∑ j, ℓ j - ∑ j, (ℓ j - c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h1 : |∑ j, (ℓ j - c)| ≤ n * B := by
    calc _ ≤ ∑ j, |ℓ j - c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, B := Finset.sum_le_sum fun j _ => hb j
      _ = n * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : |(n : ℝ) * c| ≤ S + n * B := by
    rw [e]
    exact (abs_sub_le_abs_add_abs _ _).trans (add_le_add hS h1)
  rw [abs_mul, abs_of_pos hnpos] at h2
  have h3 : (n : ℝ) * |c| ≤ n * (S + B) := by nlinarith [mul_nonneg (sub_nonneg.2 hn1) hS0]
  have hc : |c| ≤ S + B := le_of_mul_le_mul_left h3 hnpos
  calc |ℓ i| = |(ℓ i - c) + c| := by rw [sub_add_cancel]
    _ ≤ |ℓ i - c| + |c| := abs_add_le_abs_add_abs _ _
    _ ≤ B + (S + B) := add_le_add (hb i) hc
    _ = S + 2 * B := by ring

end DiscreteGroups.T1.G.CP

end
end

-- bundled from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.IntegralMulRightFd
section
noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def OrthLie : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ φ : Sm E n, IsAutForm φ → Orth D π φ → ∀ X, Orth D π (act (Op.lie X) φ)

theorem countable_GL (m : ℕ) : Countable (GL (Fin m) E) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin m) (Fin m) E) := inferInstanceAs (Countable (Fin m → Fin m → E))
  exact Function.Injective.countable (f := (Units.val : GL (Fin m) E → Matrix (Fin m) (Fin m) E)) fun a b hab => Units.ext hab

theorem countable_ratH : Countable (ratH E n 0) := by
  have := countable_GL (E := E) n
  have := countable_GL (E := E) 0
  show Countable ((ratGL E n).prodMap (ratGL E 0)).range
  exact (MonoidHom.rangeRestrict_surjective ((ratGL E n).prodMap (ratGL E 0))).countable

theorem logAbs_det_mul (x y : GA E n) : logAbs (x * y).val.det = logAbs x.val.det + logAbs y.val.det := by
  rw [Units.val_mul, Matrix.det_mul]
  exact (D1.logAbsBasic E).2.1 _ _ (Matrix.isUnits_det_units x) (Matrix.isUnits_det_units y)

theorem logAbs_ratGL (γ : GL (Fin n) E) : logAbs (ratGL E n γ).val.det = 0 := by
  have h : (ratGL E n γ).val.det = algebraMap E (Ad E) γ.val.det := by
    rw [RingHom.map_det]; rfl
  rw [h]
  exact (D1.logAbsBasic E).2.2 _ (Matrix.isUnits_det_units γ).ne_zero

theorem ldet_mul_right (x : H E n 0) (g : GA E n) :
    ldet (x * ((g, 1) : H E n 0)) = ldet x + logAbs g.val.det := by
  show logAbs (x.1 * g).val.det = logAbs x.1.val.det + logAbs g.val.det
  exact logAbs_det_mul _ _

theorem fst_ratH (γ : ratH E n 0) : ∃ γ₁ : GL (Fin n) E, (γ : H E n 0).1 = ratGL E n γ₁ := by
  have hm := γ.2
  change (γ : H E n 0) ∈ ((ratGL E n).prodMap (ratGL E 0)).range at hm
  rw [MonoidHom.mem_range] at hm
  obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := hm
  exact ⟨γ₁, by rw [← hγ]; rfl⟩

theorem ldet_ratH_mul (γ : ratH E n 0) (x : H E n 0) : ldet ((γ : H E n 0) * x) = ldet x := by
  obtain ⟨γ₁, h1⟩ := fst_ratH γ
  show logAbs ((γ : H E n 0).1 * x.1).val.det = logAbs x.1.val.det
  rw [h1, logAbs_det_mul, logAbs_ratGL, zero_add]

theorem integral_mul_right_fd (D : Dom E n 0) (h : H E n 0) (f : H E n 0 → ℂ)
    (hf : ∀ (γ : ratH E n 0) x, f ((γ : H E n 0) * x) = f x) :
    ∫ x, f (x * h) ∂D.ν = ∫ x, f x ∂D.ν := by
  have := D.haar.1
  have := D.haar.2.1
  have : BorelSpace (H E n 0) := ⟨rfl⟩
  have : MeasurableConstSMul (ratH E n 0) (H E n 0) := ⟨fun γ => measurable_const_mul (γ : H E n 0)⟩
  have : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have := countable_ratH (E := E) (n := n)
  have hmp : MeasurePreserving (fun x => x * h) D.μ D.μ := measurePreserving_mul_right D.μ h
  have hme : MeasurableEmbedding (fun x : H E n 0 => x * h) := (MeasurableEquiv.mulRight h).measurableEmbedding
  set s : Set (H E n 0) := (fun y => y * h⁻¹) ⁻¹' D.F with hs_def
  have hs : (fun x => x * h) ⁻¹' s = D.F := by
    ext x
    simp [hs_def]
  have hfd : IsFundamentalDomain (ratH E n 0) s D.μ :=
    D.fd.preimage_of_equiv (measurePreserving_mul_right D.μ h⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id fun γ y => mul_assoc (γ : H E n 0) y h⁻¹
  calc ∫ x, f (x * h) ∂D.ν = ∫ x in (fun x => x * h) ⁻¹' s, f (x * h) ∂D.μ := by rw [hs]; rfl
    _ = ∫ y in s, f y ∂D.μ := hmp.setIntegral_preimage_emb hme f s
    _ = ∫ y in D.F, f y ∂D.μ := hfd.setIntegral_eq D.fd fun γ x => hf γ x
    _ = ∫ x, f x ∂D.ν := rfl

theorem orth_rt (D : Dom E n 0) (π : CuspSub E n) (g : GA E n) (hg : ∀ ψ ∈ π.V, rt E n (g⁻¹) ψ ∈ π.V)
    {φ : Sm E n} (hφ : IsAutForm φ) (h : Orth D π φ) : Orth D π (rt E n g φ) := by
  intro ψ hψ u hu hsu
  set c := logAbs g.val.det with hc
  have key := integral_mul_right_fd D ((g, 1) : H E n 0)
    (fun y => starRingEnd ℂ (ψ.1 (y.1 * g⁻¹) * u (ldet y - c)) * φ.1 y.1) (by
      intro γ y
      obtain ⟨γ₁, h1⟩ := fst_ratH γ
      have e1 : ((γ : H E n 0) * y).1 = ratGL E n γ₁ * y.1 := by rw [Prod.fst_mul, h1]
      simp only [e1, ldet_ratH_mul, mul_assoc]
      rw [(π.cusp ψ hψ).1.left, hφ.left])
  have e2 : prg D ψ u (rt E n g φ) = ∫ x, (fun y : H E n 0 =>
      starRingEnd ℂ (ψ.1 (y.1 * g⁻¹) * u (ldet y - c)) * φ.1 y.1) (x * ((g, 1) : H E n 0)) ∂D.ν := by
    unfold prg
    congr 1
    funext x
    have e3 : (x * ((g, 1) : H E n 0)).1 = x.1 * g := rfl
    simp only [e3, ldet_mul_right, hc, add_sub_cancel_right, mul_inv_cancel_right]
    rfl
  rw [e2, key]
  exact h (rt E n (g⁻¹) ψ) (hg ψ hψ) (fun t => u (t - c)) (hu.comp (contDiff_id.sub contDiff_const))
    (hsu.comp_homeomorph (Homeomorph.subRight c))

theorem orth_fin (D : Dom E n 0) (π : CuspSub E n) {φ : Sm E n} (hφ : IsAutForm φ) (h : Orth D π φ)
    (k : GL (Fin n) (Af E)) : Orth D π (act (Op.fin k) φ) := by
  refine orth_rt D π (finGL E n k) (fun ψ hψ => ?_) hφ h
  have e : rt E n ((finGL E n k)⁻¹) ψ = act (Op.fin k⁻¹) ψ := by
    show rt E n ((finGL E n k)⁻¹) ψ = rt E n (finGL E n k⁻¹) ψ
    rw [map_inv (finGL E n) k]
  rw [e]
  exact π.stable _ ψ hψ

theorem orth_cpt (D : Dom E n 0) (π : CuspSub E n) {φ : Sm E n} (hφ : IsAutForm φ) (h : Orth D π φ)
    (k : Kinf E n) : Orth D π (act (Op.cpt k) φ) := by
  refine orth_rt D π (infGL E n (Unitary.toUnits k)) (fun ψ hψ => ?_) hφ h
  have e : rt E n ((infGL E n (Unitary.toUnits k))⁻¹) ψ = act (Op.cpt k⁻¹) ψ := by
    show rt E n ((infGL E n (Unitary.toUnits k))⁻¹) ψ = rt E n (infGL E n (Unitary.toUnits k⁻¹)) ψ
    rw [map_inv (Unitary.toUnits (R := Matrix (Fin n) (Fin n) (Cinf E))) k, map_inv (infGL E n)]
  rw [e]
  exact π.stable _ ψ hψ

theorem rOrthAct (hL : OrthLie) : OrthAct := by
  intro E _ _ _ n hn D π hθ φ hφ h o
  cases o with
  | fin k => exact orth_fin D π hφ h k
  | cpt k => exact orth_cpt D π hφ h k
  | lie X => exact hL E n hn D π hθ φ hφ h X

end DiscreteGroups.T1.G

end
end

-- bundled from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvOf
section
noncomputable section

open NumberField MeasureTheory
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal InnerProductSpace

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

theorem memLp_rt (X : PositivityTheory.Rg.BcB.E1.Ctx) (hr : X.μ.IsMulRightInvariant) {f : X.G → ℂ}
    (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y) (hf : MemLp f 2 X.ν) (z : X.G) :
    MemLp (fun x => f (x * z)) 2 X.ν := by
  haveI := hr
  have hνμ : X.ν ≪ X.μ := Measure.absolutelyContinuous_of_le (Measure.restrict_le_self : X.μ.restrict X.F ≤ X.μ)
  refine ⟨((aesm_of_inv X hinv hf.1).comp_measurePreserving (measurePreserving_mul_right X.μ z)).mono_ac hνμ, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
    lint_rt X hr (g := fun y => ‖f y‖ₑ ^ (2 : ℝ≥0∞).toReal) (fun γ y => by simp only [hinv γ y]) z,
    ← eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
  exact hf.2

theorem piInv_of (hC : PiClosureInv) : PiInv := by
  intro E _ _ _ n hn D π hθ ι _ Φ T hΦ hT
  classical
  let X := PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D
  have hr : X.μ.IsMulRightInvariant := D.haar.2.1
  have hdet : ∀ g : GA E n, IsUnit (g : Matrix (Fin n) (Fin n) (Ad E)).det := fun g => by
    simp
  have hldet : ∀ (γ : ratH E n 0) (y : H E n 0), ldet ((γ : H E n 0) * y) = ldet y := by
    intro γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    have hb := PositivityTheory.Rg.BcB.D1.logAbsBasic E
    have hd : ((ratGL E n γ₁ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)).det =
        algebraMap E (Ad E) (γ₁ : Matrix (Fin n) (Fin n) E).det := by
      simp [ratGL, RingHom.map_det]
    have hne : (γ₁ : Matrix (Fin n) (Fin n) E).det ≠ 0 := by
      simpa using (Matrix.GeneralLinearGroup.det γ₁).ne_zero
    simp only [ldet, Prod.fst_mul, h1]
    rw [Units.val_mul, Matrix.det_mul, hb.2.1 _ _ (hdet _) (hdet _), hd, hb.2.2 _ hne, zero_add]
  have hpsi0 : True := trivial
  have hpsi : ∀ ψ ∈ π.V, ∀ (γ : ratH E n 0) (y : H E n 0), ψ.1 ((γ : H E n 0) * y).1 = ψ.1 y.1 := by
    intro ψ hψ γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (π.cusp ψ hψ).1.left γ₁ y.1
  have key : ∀ g : Hs (ι := ι) D, IsPiVec D π g → T g ∈ piSp D π ι := by
    intro g hg
    choose ψ hψ u hu hu' hgu using hg
    set Ft : ι → H E n 0 → ℂ := fun j x => (ψ j).1 x.1 * u j (ldet x) with hFt
    have hinv : ∀ j, ∀ γ : ratH E n 0, ∀ y : H E n 0, Ft j ((γ : H E n 0) * y) = Ft j y := fun j γ y => by
      show (ψ j).1 ((γ : H E n 0) * y).1 * u j (ldet ((γ : H E n 0) * y)) = (ψ j).1 y.1 * u j (ldet y)
      rw [hpsi _ (hψ j) γ y, hldet γ y]
    have hmem : ∀ j, MemLp (Ft j) 2 X.ν := fun j => (Lp.memLp (g j)).ae_eq (hgu j)
    rw [← Submodule.orthogonal_orthogonal (piSp D π ι), Submodule.mem_orthogonal]
    intro h hh
    have hz : ∀ i j (z : H E n 0),
        ∫ x, starRingEnd ℂ ((h i : H E n 0 → ℂ) x) * Ft j (x * z) ∂D.ν = 0 := by
      intro i j z
      have hw := memLp_rt X hr (hinv j) (hmem j) z
      let w : Lp ℂ 2 D.ν := hw.toLp _
      let v : Hs (ι := ι) D := WithLp.toLp 2 (Pi.single i w)
      have hvl : ∀ l, v l = (Pi.single i w : ι → Lp ℂ 2 D.ν) l := fun l => rfl
      have hv : v ∈ piSp D π ι := by
        refine hC E n hn D π hθ ι (fun l => if l = i then ψ j else 0) (fun l => if l = i then u j else 0) z v ?_ ?_
        · intro l
          split_ifs
          · exact ⟨hψ j, hu j, hu' j⟩
          · exact ⟨Submodule.zero_mem _, continuous_zero, HasCompactSupport.zero⟩
        · intro l
          rw [hvl]
          by_cases hl : l = i
          · subst hl
            rw [Pi.single_eq_same]
            filter_upwards [hw.coeFn_toLp] with x hx
            simp only [if_pos rfl]
            exact (show (w : H E n 0 → ℂ) x = Ft j (x * z) from hx)
          · rw [Pi.single_eq_of_ne hl]
            filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := D.ν)] with x hx
            rw [hx]
            simp only [if_neg hl, Submodule.coe_zero, ZeroMemClass.coe_zero, Pi.zero_apply, zero_mul]
      have h0 : ⟪h, v⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal hv hh
      rw [PiLp.inner_apply, Finset.sum_eq_single i (fun l _ hl => by rw [hvl, Pi.single_eq_of_ne hl, inner_zero_right])
        (fun hi => absurd (Finset.mem_univ i) hi), hvl, Pi.single_eq_same, MeasureTheory.L2.inner_def] at h0
      rw [← h0]
      refine integral_congr_ae ?_
      filter_upwards [hw.coeFn_toLp] with x hx
      rw [show (w : H E n 0 → ℂ) x = Ft j (x * z) from hx, RCLike.inner_apply, mul_comm]
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [MeasureTheory.L2.inner_def]
    have hP := fun j => pair_zero X hr PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable (hΦ i j) (hinv j) (hmem j)
      (Lp.memLp (h i)) (hz i j)
    calc ∫ x, ⟪(h i : H E n 0 → ℂ) x, (T g i : H E n 0 → ℂ) x⟫_ℂ ∂D.ν
        = ∫ x, ∑ j, starRingEnd ℂ ((h i : H E n 0 → ℂ) x) *
            ∫ y, kerH (Φ i j) x y * Ft j y ∂D.ν ∂D.ν := by
          refine integral_congr_ae ?_
          filter_upwards [hT g i] with x hx
          rw [hx, RCLike.inner_apply, mul_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          exact integral_congr_ae ((hgu j).mono fun y hy => by simp only [hy, hFt])
      _ = ∑ j, ∫ x, starRingEnd ℂ ((h i : H E n 0 → ℂ) x) * ∫ y, kerH (Φ i j) x y * Ft j y ∂D.ν ∂D.ν :=
          integral_finset_sum _ fun j _ => (hP j).1
      _ = 0 := Finset.sum_eq_zero fun j _ => (hP j).2
  intro f hf
  have hle : Submodule.span ℂ {f | IsPiVec D π f} ≤ (piSp D π ι).comap (T : Hs (ι := ι) D →ₗ[ℂ] Hs (ι := ι) D) :=
    Submodule.span_le.2 fun g hg => key g hg
  have hcl : IsClosed (((piSp D π ι).comap (T : Hs (ι := ι) D →ₗ[ℂ] Hs (ι := ι) D)) : Set (Hs (ι := ι) D)) :=
    (show IsClosed (piSp D π ι : Set (Hs (ι := ι) D)) from Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact Submodule.topologicalClosure_minimal _ hle hcl hf

end DiscreteGroups.T1.G

end
end

