import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearIsQuotIntTInt
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app app_coe)
open scoped Topology

noncomputable section
namespace GlobalTheory.PosOne.RrLin

theorem exists_open_translations {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] {Φ : M → ℂ} (hΦ : Φ ∈ SB M) :
    ∃ Λ : AddSubgroup M, IsOpen (Λ : Set M) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  let Λ : AddSubgroup M :=
    { carrier := {y | ∀ x, Φ (x + y) = Φ x}
      zero_mem' := fun x => by simp
      add_mem' := fun {y z} hy hz x => by rw [← add_assoc, hz, hy]
      neg_mem' := fun {y} hy x => by rw [← hy (x + -y)]; simp }
  refine ⟨Λ, Λ.isOpen_of_mem_nhds (g := 0) ?_, fun x y hy => hy x⟩
  have h1 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + y) = Φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : M × M => (Φ (q.2 + q.1), Φ q.2) :=
      (hΦ.1.comp_continuous (continuous_snd.add continuous_fst)).prodMk
        (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h2 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + -y) = Φ x := by
    have ht : Filter.Tendsto (fun y : M => -y) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := M)).tendsto 0
    exact ht.eventually h1
  filter_upwards [h1, h2] with y hs hs' x
  by_cases hx : x ∈ tsupport Φ
  · exact hs x hx
  by_cases hx' : x + y ∈ tsupport Φ
  · rw [← hs' _ hx']; simp
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem exists_isQuotInt_tInt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} (hp : 1 ≤ p) (hpc : p ≤ c) {ψ : AddChar k Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ))
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} (hσ : IsSmoothRep σ)
    {B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hB : BilPos ψ μ p σ B) (F : A)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    ∃ z, IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) z := by
  have hE := (opE_SB_and_linear k n n' c p ψ hψ ν).1
  let E : GL (n ⊕ Fin c) k → SB (Matrix n n' k) := fun h =>
    ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩
  set f := tInt ψ ν μ p σ B F Φ.1 with hf
  have hfE : ∀ h, f h = B (E h) (σ h F) := fun h => by
    rw [hf, tInt]
    exact congrArg (fun l : A →ₗ[ℂ] ℂ => l (σ h F)) (app_coe B (E h))
  have hmul : ∀ (g h : GL (n ⊕ Fin c) k) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ),
      om μ 1 (g * h) Ψ = om μ 1 g (om μ 1 h Ψ) := fun g h Ψ => by
    rw [← om_mul, one_mul]
  refine (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG f).2 ?_ ?_ ?_
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro h
    have hU : IsOpen ({u : GL (n ⊕ Fin c) k | om μ 1 u Φ.1 = Φ.1} ∩ {u | σ u F = F}) :=
      ((isOpen_stabilizer_om hμ Φ.2).preimage (Continuous.prodMk_right 1)).inter (hσ F)
    have ht : Filter.Tendsto (fun y : GL (n ⊕ Fin c) k => h⁻¹ * y) (𝓝 h) (𝓝 1) := by
      simpa using (continuous_const_mul h⁻¹).tendsto h
    filter_upwards [ht.eventually (hU.mem_nhds ⟨om_one μ _, by simp⟩)] with y hy
    obtain ⟨u, rfl⟩ : ∃ u, y = h * u := ⟨h⁻¹ * y, by simp⟩
    rw [inv_mul_cancel_left] at hy
    have h1 : om μ 1 u Φ.1 = Φ.1 := hy.1
    have h2 : σ u F = F := hy.2
    have h3 : E (h * u) = E h := Subtype.ext (by
      show opE ψ ν p (om μ 1 (h * u) Φ.1) = opE ψ ν p (om μ 1 h Φ.1)
      rw [hmul, h1])
    rw [hfE h, hfE (h * u), h3, map_mul, Module.End.mul_apply, h2]
  · obtain ⟨Λ, hΛ, hΛ'⟩ := exists_open_translations Φ.2
    obtain ⟨Ω, hΩ, H⟩ := opE_support_compact_mod_R k n n' c p hp hpc ψ hψ hψ1 ν (tsupport Φ.1)
      Φ.2.2 Λ hΛ
    refine ⟨Ω, hΩ, fun h hh => ?_⟩
    have hne : E h ≠ 0 := fun h0 => hh (by rw [hfE, h0]; simp)
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE ψ ν p (om μ 1 h Φ.1) x₀ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (Subtype.ext (funext hc))
    exact H μ Φ.1 (subset_tsupport _) hΛ' (fun _ => 1) (IsLocallyConstant.const 1) h x₀
      (by simpa using hx₀)
  · intro x u hu h
    set a : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) with ha
    let Ψ : SB (Matrix n n' k) := ⟨om μ 1 x (E h).1, om_mem_SB μ 1 x (E h).2⟩
    have h1 : E (embX c x * u * h) = (a * (ψ (-simpleSum u) : ℂ)) • Ψ := by
      apply Subtype.ext
      show opE ψ ν p (om μ 1 (embX c x * u * h) Φ.1) =
        (a * (ψ (-simpleSum u) : ℂ)) • om μ 1 x (opE ψ ν p (om μ 1 h Φ.1))
      rw [mul_assoc, hmul, (opE_om_embX k n n' c p hp hpc ψ ν μ _).1, hmul,
        opE_om_target_unipotent k n n' c p hp hpc ψ ν μ _ u hu]
      funext y
      simp only [om, Pi.smul_apply, smul_eq_mul, ha]
      ring
    have h3 : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; simp
    have h4 : a * a =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) := by
      rw [ha, ← Complex.ofReal_mul, ← Real.rpow_add (nabs_pos _ _)]
      congr 2
      ring
    have h5 := hB.1 (E h) u hu (σ h F)
    have h6 := hB.2 x (E h) Ψ (σ u (σ h F)) rfl
    rw [hfE, hfE, h1, map_smul, LinearMap.smul_apply, map_mul, map_mul,
      Module.End.mul_apply, Module.End.mul_apply, h6, h5, ← h4, ← ha, smul_eq_mul]
    linear_combination (a * a * B (E h) (σ h F)) * h3

end GlobalTheory.PosOne.RrLin

namespace GlobalTheory.PosOne.RrLin
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem exists_linear_isQuotInt_tInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ p σ B) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ'), ∃ Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) (Rr Φ)) ∧ IsNEquiv ψ p ρ' Rr := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hpc ψ hψ hψ1 ν _ μ hμ μX _ μG _ A _ _ σ hσ B hB F ρ' hρ'
  have uniq := (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG · |>.1)
  have hE := (opE_SB_and_linear k n n' c p ψ hψ ν).1

  have hfE : ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) h,
      tInt ψ ν μ p σ B F Φ.1 h =
        B ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩ (σ h F) := fun Φ h => by
    rw [tInt]
    exact congrArg (fun l : A →ₗ[ℂ] ℂ => l (σ h F)) (app_coe B ⟨_, hE _ (om_mem_SB μ 1 h Φ.2)⟩)

  have hlinf : ∀ (a : ℂ) (Φ Ψ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      tInt ψ ν μ p σ B F (a • Φ + Ψ).1 = fun h => a * tInt ψ ν μ p σ B F Φ.1 h + tInt ψ ν μ p σ B F Ψ.1 h := by
    intro a Φ Ψ
    funext h
    rw [hfE, hfE, hfE, ← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.add_apply, ← map_smul, ← map_add]
    congr 2
    apply Subtype.ext
    show opE ψ ν p (om μ 1 h (a • Φ.1 + Ψ.1)) =
      a • opE ψ ν p (om μ 1 h Φ.1) + opE ψ ν p (om μ 1 h Ψ.1)
    have e : om μ 1 h (a • Φ.1 + Ψ.1) = a • om μ 1 h Φ.1 + om μ 1 h Ψ.1 := by
      funext y; simp only [om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact (opE_SB_and_linear k n n' c p ψ hψ ν).2 a _ (om_mem_SB μ 1 h Φ.2) _ (om_mem_SB μ 1 h Ψ.2)
  have hex := fun Φ => exists_isQuotInt_tInt hp hpc hψ hψ1 ν hμ μX μG hσ hB F Φ
  choose Rr hRr using hex
  have hlin : ∀ (a : ℂ) Φ Ψ, Rr (a • Φ + Ψ) = a * Rr Φ + Rr Ψ := fun a Φ Ψ => by
    refine uniq _ _ _ (hRr _) ?_
    rw [hlinf]
    exact GlobalTheory.RootEx.QuotLinear.isQuotInt_linear k n c p hp hpc ν μX μG _ _ a _ _ (hRr Φ) (hRr Ψ)
  have h0 : Rr 0 = 0 := by simpa using hlin 1 0 0
  let RL : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ :=
    { toFun := Rr
      map_add' := fun Φ Ψ => by simpa using hlin 1 Φ Ψ
      map_smul' := fun a Φ => by simpa [h0] using hlin a Φ 0 }
  refine ⟨RL, hRr, fun g hg Φ => ?_⟩
  show Rr (ρ' g Φ) = (ψ (simpleSum g) : ℂ) * Rr Φ
  have e : tInt ψ ν μ p σ B F (ρ' g Φ).1 = tInt ψ ν μ p σ B F ((ψ (simpleSum g) : ℂ) • Φ + 0).1 := by
    funext h
    rw [hfE, hfE]
    congr 2
    apply Subtype.ext
    show opE ψ ν p (om μ 1 h (ρ' g Φ).1) = opE ψ ν p (om μ 1 h ((ψ (simpleSum g) : ℂ) • Φ.1 + 0))
    have e1 : om μ 1 h (om μ g 1 Φ.1) = om μ g 1 (om μ 1 h Φ.1) := by
      rw [← om_mul, ← om_mul, one_mul, mul_one, mul_one, one_mul]
    rw [hρ', e1, GlobalTheory.RootExSource.opE_om_source k n n' c p hp hpc ψ ν μ _ g hg, add_zero]
    have e2 : om μ 1 h ((ψ (simpleSum g) : ℂ) • Φ.1) = (ψ (simpleSum g) : ℂ) • om μ 1 h Φ.1 := by
      funext y; simp only [om, Pi.smul_apply, smul_eq_mul]; ring
    rw [e2]
    funext x
    simp only [opE, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  have e3 : Rr (ρ' g Φ) = Rr ((ψ (simpleSum g) : ℂ) • Φ + 0) := uniq _ _ _ (hRr _) (e ▸ hRr _)
  rw [e3, hlin, h0, add_zero]

end GlobalTheory.PosOne.RrLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesBorelSphericalIntegralCosets
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.HeckeSeries

section Cosets

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {p : 𝒪[k]}

theorem ord_det_of_mem_KO {y : GL (Fin n) k} (hy : y ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det y) = 0 := by
  have hq : (1 : ℝ) < resCard k := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have h1 := GlobalTheory.LGrp.nabs_eq_zpow (Matrix.GeneralLinearGroup.det y)
  rw [GlobalTheory.LGrp.nabs_det_of_mem_KO hy] at h1
  have h2 : ((resCard k : ℝ)) ^ (-ord k (Matrix.GeneralLinearGroup.det y)) = (resCard k : ℝ) ^ (0 : ℤ) := by
    rw [← h1, zpow_zero]
  exact neg_eq_zero.1 (zpow_right_injective₀ (by positivity) hq.ne' h2)

end Cosets

open MeasureTheory ValuativeRel in
private theorem hermGL_coset_out_entries_integral {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {p : 𝒪[k]} (hp : Irreducible p)
    (a : Fin n → ℕ) (c : _root_.GlobalTheory.SatakeBound.HermIdx p a) :
    ∀ i j, (((_root_.GlobalTheory.SatakeBound.hermGL hp a c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n)).out :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (_root_.GlobalTheory.SplitWeil.KO k (Fin n))
    (_root_.GlobalTheory.SatakeBound.hermGL hp a c)
  have hint := ((_root_.GlobalTheory.SplitFlip.mem_KO_iff (h : GL (Fin n) k)).1 h.2).1
  intro i j
  rw [hh, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
  refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ ?_ (hint l j)
  rw [_root_.GlobalTheory.SatakeBound.val_hermGL]
  exact ((_root_.GlobalTheory.SatakeBound.hermMat p a c) i l).2

open MeasureTheory ValuativeRel in
private theorem exists_hermGL_coset_eq_of_integral {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {p : 𝒪[k]} (hp : Irreducible p)
    (g : GL (Fin n) k) (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k]) :
    ∃ a c, ((_root_.GlobalTheory.SatakeBound.hermGL hp a c : GL (Fin n) k) :
        GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n)) = (g : GL (Fin n) k ⧸ _) := by
  obtain ⟨b, hb, w, hw, hgbw⟩ :=
    _root_.GlobalTheory.SplitWeil.iwasawa_blockTriangular k (Fin n) (fun i => (i : ℕ)) g
  have hbint : ∀ i j, (b : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    have hbg : b = g * w⁻¹ := by rw [hgbw]; group
    have hwinv := ((_root_.GlobalTheory.SplitFlip.mem_KO_iff w).1 hw).2
    intro i j
    rw [hbg, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hg i l) (hwinv l j)
  let b' : Matrix (Fin n) (Fin n) 𝒪[k] :=
    Matrix.of fun i j => ⟨(b : Matrix (Fin n) (Fin n) k) i j, hbint i j⟩
  have hlow : ∀ i j, j < i → b' i j = 0 := fun i j h => Subtype.ext (hb h)
  have hdiag : ∀ i, b' i i ≠ 0 := by
    intro i h
    have hb' : (b : Matrix (Fin n) (Fin n) k).BlockTriangular id := fun i j h => hb h
    have hdet := Matrix.det_of_upperTriangular hb'
    have hne : (b : Matrix (Fin n) (Fin n) k).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    apply hne
    rw [hdet]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (congrArg Subtype.val h)
  obtain ⟨a, c, W, hW⟩ := _root_.GlobalTheory.SatakeBound.exists_hermMat hp b' hlow hdiag
  refine ⟨a, c, ?_⟩
  let Wk : GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) W
  have hWk : Wk ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n) := by
    rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
    constructor
    · intro i j
      exact ((W : Matrix (Fin n) (Fin n) 𝒪[k]) i j).2
    · intro i j
      rw [show Wk⁻¹ = Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) W⁻¹ from (map_inv _ _).symm]
      exact ((W⁻¹ : GL (Fin n) 𝒪[k]) i j).2
  have hhnf : _root_.GlobalTheory.SatakeBound.hermGL hp a c = b * Wk := by
    ext i j
    rw [_root_.GlobalTheory.SatakeBound.val_hermGL, hW, Matrix.GeneralLinearGroup.coe_mul, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  rw [hhnf, hgbw, QuotientGroup.eq]
  convert mul_mem (inv_mem hWk) hw using 1
  group

open MeasureTheory ValuativeRel in
private theorem ord_eq_of_nabs_eq_resCard_zpow_neg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {x : kˣ} {m : ℤ}
    (hx : _root_.GlobalTheory.SplitWeil.nabs k x = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m)) :
    _root_.GlobalTheory.SmGL.ord k x = m := by
  have hq : (1 : ℝ) < _root_.GlobalTheory.SplitWeil.resCard k := by
    exact_mod_cast _root_.GlobalTheory.SplitWeil.one_lt_resCard k
  rw [_root_.GlobalTheory.LGrp.nabs_eq_zpow] at hx
  have := zpow_right_injective₀ (by linarith) hq.ne' hx
  linarith

open MeasureTheory ValuativeRel in
private theorem ord_det_hermGL_mul_eq_sum {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {p : 𝒪[k]} (hp : Irreducible p)
    (a : Fin n → ℕ) (c : _root_.GlobalTheory.SatakeBound.HermIdx p a) {w : GL (Fin n) k}
    (hw : w ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n)) :
    _root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.SatakeBound.hermGL hp a c * w)) =
      ∑ i, (a i : ℤ) := by
  have hp0 : (p : k) ≠ 0 := by
    intro h
    exact hp.ne_zero (Subtype.ext h)
  set u : kˣ := Units.mk0 (p : k) hp0 with hu
  have hu1 : _root_.GlobalTheory.SmGL.ord k u = 1 := by
    apply ord_eq_of_nabs_eq_resCard_zpow_neg
    rw [_root_.GlobalTheory.SplitWeil.nabs_uniformiser hp (x := u) rfl, zpow_neg, zpow_one]
  have hupow : ∀ m : ℕ, _root_.GlobalTheory.SmGL.ord k (u ^ m) = m := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero]
      exact _root_.GlobalTheory.SmGL.ord_eq_zero_iff.2 (by simp)
    | succ m ih => rw [pow_succ, _root_.GlobalTheory.SmGL.ord_mul, ih, hu1]; push_cast; ring
  have hw0 : _root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det w) = 0 := by
    apply ord_eq_of_nabs_eq_resCard_zpow_neg
    rw [_root_.GlobalTheory.GLDoubling.nabs_det_of_mem_KO hw]
    simp
  have hdet : Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.SatakeBound.hermGL hp a c) = u ^ (∑ i, a i) := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, _root_.GlobalTheory.SatakeBound.val_hermGL, RingHom.mapMatrix_apply,
      show ((_root_.GlobalTheory.SatakeBound.hermMat p a c).map (algebraMap 𝒪[k] k)).det =
        algebraMap 𝒪[k] k (_root_.GlobalTheory.SatakeBound.hermMat p a c).det from (RingHom.map_det _ _).symm,
      _root_.GlobalTheory.SatakeBound.det_hermMat]
    simp [u]
    rfl
  rw [map_mul, _root_.GlobalTheory.SmGL.ord_mul, hw0, hdet, hupow]
  push_cast
  ring

open MeasureTheory ValuativeRel in
private theorem hasSum_prod_pow_eq_prod_one_sub_inv : ∀ (n : ℕ) (β : Fin n → ℂ), (∀ i, ‖β i‖ < 1) →
    Summable (fun a : Fin n → ℕ => ‖∏ i, β i ^ a i‖) ∧
      HasSum (fun a : Fin n → ℕ => ∏ i, β i ^ a i) (∏ i, (1 - β i)⁻¹)
  | 0, β, _ => by
    refine ⟨Summable.of_finite, ?_⟩
    simpa using (hasSum_fintype (fun a : Fin 0 → ℕ => (1 : ℂ)))
  | n + 1, β, hβ => by
    obtain ⟨hs, hh⟩ := hasSum_prod_pow_eq_prod_one_sub_inv n (fun i => β i.succ) (fun i => hβ i.succ)
    have hg : HasSum (fun m : ℕ => β 0 ^ m) (1 - β 0)⁻¹ := hasSum_geometric_of_norm_lt_one (hβ 0)
    have hgn : Summable (fun m : ℕ => ‖β 0 ^ m‖) := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hβ 0)
    have hprodn := Summable.mul_norm hgn hs
    have hprod := hg.mul hh (Summable.of_norm hprodn)
    let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) := Fin.consEquiv fun _ => ℕ
    have hfe : ∀ x : ℕ × (Fin n → ℕ), ∏ i, β i ^ (e x) i = β 0 ^ x.1 * ∏ i, β i.succ ^ x.2 i := by
      intro x
      rw [Fin.prod_univ_succ]
      simp [e, Fin.consEquiv]
    refine ⟨?_, ?_⟩
    · refine (e.summable_iff.1 ?_)
      refine hprodn.congr fun x => ?_
      simp only [Function.comp_apply, hfe]
    · rw [Fin.prod_univ_succ]
      refine (e.hasSum_iff.1 ?_)
      refine hprod.congr_fun fun x => ?_
      simp only [Function.comp_apply, hfe]

open MeasureTheory ValuativeRel in

theorem _root_.GlobalTheory.HeckeSeries.hasSum_integral_cosets : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ)
    (φ : GL (Fin n) k → ℂ), _root_.GlobalTheory.SatakeBound.IsBorelSph k γ φ → ∀ X : ℂ,
    (∀ i : Fin n, ‖(_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1) →
    HasSum (fun c : {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ (_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out)
      (∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) := by
  intro k _ _ _ _ n γ φ hφ X hX
  classical
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  let F : (Σ a : Fin n → ℕ, _root_.GlobalTheory.SatakeBound.HermIdx p a) →
      {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} := fun x =>
    ⟨(_root_.GlobalTheory.SatakeBound.hermGL hp x.1 x.2 : GL (Fin n) k ⧸ _), hermGL_coset_out_entries_integral hp x.1 x.2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun x y h => _root_.GlobalTheory.SatakeBound.hermGL_injective hp (congrArg Subtype.val h), fun s => ?_⟩
    obtain ⟨a, c, h⟩ := exists_hermGL_coset_eq_of_integral hp s.1.out s.2
    refine ⟨⟨a, c⟩, Subtype.ext ?_⟩
    change ((_root_.GlobalTheory.SatakeBound.hermGL hp a c : GL (Fin n) k) : GL (Fin n) k ⧸ _) = s.1
    rw [h]
    exact QuotientGroup.out_eq' s.1
  rw [← (Equiv.ofBijective F hF).hasSum_iff]
  set β : Fin n → ℂ := fun i => (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X
    with hβ
  have hterm : ∀ x : (Σ a : Fin n → ℕ, _root_.GlobalTheory.SatakeBound.HermIdx p a),
      X ^ (_root_.GlobalTheory.SmGL.ord k
        (Matrix.GeneralLinearGroup.det (F x).1.out)).toNat * φ (F x).1.out =
        ∏ i, (γ i * X) ^ x.1 i := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (_root_.GlobalTheory.SplitWeil.KO k (Fin n))
      (_root_.GlobalTheory.SatakeBound.hermGL hp x.1 x.2)
    have hord := ord_det_hermGL_mul_eq_sum hp x.1 x.2 h.2
    have hval := _root_.GlobalTheory.SatakeBound.apply_hermGL hp hφ x.1 x.2
    change X ^ (_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det
      (Quotient.out ((_root_.GlobalTheory.SatakeBound.hermGL hp x.1 x.2 : GL (Fin n) k) :
        GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n))))).toNat *
      φ (Quotient.out ((_root_.GlobalTheory.SatakeBound.hermGL hp x.1 x.2 : GL (Fin n) k) :
        GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n))) = _
    rw [hval, hh, hord, show (∑ i, (x.1 i : ℤ)) = ((∑ i, x.1 i : ℕ) : ℤ) by push_cast; rfl,
      Int.toNat_natCast, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [mul_pow, mul_comm]
  have hcard : ∀ a : Fin n → ℕ, (Nat.card (_root_.GlobalTheory.SatakeBound.HermIdx p a) : ℂ) *
      ∏ i, (γ i * X) ^ a i = ∏ i, β i ^ a i := by
    intro a
    rw [_root_.GlobalTheory.SatakeBound.card_hermIdx hp a]
    push_cast
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by simp only [hβ, mul_assoc, mul_pow]
  have hfin : ∀ a : Fin n → ℕ, Finite (_root_.GlobalTheory.SatakeBound.HermIdx p a) := by
    intro a
    apply Nat.finite_of_card_ne_zero
    rw [_root_.GlobalTheory.SatakeBound.card_hermIdx hp a]
    exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (pow_ne_zero _
      (by have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k; omega))
  obtain ⟨hsn, hsum⟩ := hasSum_prod_pow_eq_prod_one_sub_inv n β hX
  have hfib : ∀ a : Fin n → ℕ, ∑' c : _root_.GlobalTheory.SatakeBound.HermIdx p a, ∏ i, (γ i * X) ^ a i =
      ∏ i, β i ^ a i := by
    intro a
    rw [tsum_const, nsmul_eq_mul, hcard]
  have hsig : Summable (fun x : (Σ a : Fin n → ℕ, _root_.GlobalTheory.SatakeBound.HermIdx p a) =>
      ‖∏ i, (γ i * X) ^ x.1 i‖) := by
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun a => Summable.of_finite, hsn.congr fun a => ?_⟩
    symm
    show ∑' _ : _root_.GlobalTheory.SatakeBound.HermIdx p a, ‖∏ i, (γ i * X) ^ a i‖ = _
    rw [tsum_const, nsmul_eq_mul, ← hcard, norm_mul, Complex.norm_natCast]
  have hs := hsig.of_norm
  have h2 := hs.hasSum.sigma (fun a => (Summable.of_finite).hasSum)
  simp only [hfib] at h2
  have hval := hsum.unique h2
  have hfinal : HasSum (fun x : (Σ a : Fin n → ℕ, _root_.GlobalTheory.SatakeBound.HermIdx p a) =>
      ∏ i, (γ i * X) ^ x.1 i) (∏ i, (1 - β i)⁻¹) := by
    rw [hval]
    exact hs.hasSum
  refine hfinal.congr_fun fun x => ?_
  exact hterm x

end GlobalTheory.HeckeSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalZetaIntegralOpenSubgroup
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.PosOne

theorem covers_opE_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (J : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (J : Set (GL (n ⊕ Fin c) k))) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), ∃ T, Covers p J T fun h => opE ψ ν p (om μ 1 h Φ.1) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψc hψ ν _ μ _ J hJ Φ
  classical
  obtain ⟨Λ, hΛ, hper⟩ := exists_isOpen_addSubgroup_add_eq Φ.2.1 Φ.2.2
  obtain ⟨Ω, hΩ, hcov⟩ := opE_support_compact_mod_R k n n' c p hp1 hpc ψ hψc hψ ν (tsupport Φ.1) Φ.2.2 Λ hΛ
  obtain ⟨F, hF⟩ := hΩ.elim_finite_subcover (fun w : GL (n ⊕ Fin c) k => (fun g => w⁻¹ * g) ⁻¹' (J : Set _))
    (fun w => hJ.preimage (continuous_const.mul continuous_id))
    (fun w _ => Set.mem_iUnion.2 ⟨w, by simp [J.one_mem]⟩)
  let rep : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k := fun w => Quotient.out (DoubleCoset.mk (R k n c p) J w)
  have hrep : ∀ w, DoubleCoset.mk (R k n c p) J (rep w) = DoubleCoset.mk (R k n c p) J w :=
    fun w => DoubleCoset.out_eq' _ _ _
  refine ⟨F.image rep, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_image, Set.mem_image] at ha hb
    obtain ⟨w₁, -, rfl⟩ := ha
    obtain ⟨w₂, -, rfl⟩ := hb
    rw [hrep, hrep] at hab
    simp only [rep, hab]
  · intro h hh
    obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hh
    obtain ⟨r, hr, w, hw, rfl⟩ := hcov μ Φ.1 (subset_tsupport _) (fun x y hy => hper x y hy) (fun _ => 1)
      (IsLocallyConstant.const 1) h x₀ (by simpa using hx₀)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hF hw)
    obtain ⟨hiF, hiw⟩ := Set.mem_iUnion.1 hi
    refine ⟨rep i, Finset.mem_image_of_mem _ hiF, ?_⟩
    rw [hrep, eq_comm, DoubleCoset.eq]
    exact ⟨r, hr, i⁻¹ * w, hiw, by group⟩

end GlobalTheory.PosOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntEig
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalEig

theorem zonalInt_eig : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ (R : Finset (GL (Fin N) k)) (c : ℂ), (∀ m, ∑ g ∈ R, ψ (m * g) = c * ψ m) → ∀ m, ∑ g ∈ R, zonalInt μK ψ (m * g) = c * zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hμ ψ hψ R c hR m
  have hKo := (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N))
  have hcont : Continuous ψ := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_)
    have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k))) := hKo.preimage (by fun_prop)
    filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ (KO k (Fin N) : Set (GL (Fin N) k)) by
      rw [inv_mul_cancel]; exact one_mem _)] with x hx
    have := hψ g _ hx
    rwa [mul_inv_cancel_left] at this
  have hint : ∀ y, IntegrableOn (fun κ => ψ (κ * y)) (KO k (Fin N) : Set (GL (Fin N) k)) μK := fun y =>
    (hcont.comp (continuous_mul_right y)).continuousOn.integrableOn_compact GlobalTheory.SplitFlip.isCompact_KO
  simp only [zonalInt]
  rw [← integral_finset_sum _ (fun g _ => hint (m * g)), ← integral_const_mul]
  congr 1
  funext κ
  have := hR (κ * m)
  simpa only [mul_assoc] using this

end GlobalTheory.ZonalEig
end
end

