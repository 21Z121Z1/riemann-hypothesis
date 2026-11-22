import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlCharacterEqOneOfTransposeInv
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory

theorem gl_character_eq_one_of_transpose_inv (k : Type) [Field k] [Infinite k] (n : Type)
    [Fintype n] [DecidableEq n] (χ : GL n k →* NNReal)
    (h : ∀ g g' : GL n k, g'.val = (g⁻¹ : GL n k).valᵀ → χ g' = χ g) (g : GL n k) :
    χ g = 1 := by
  classical
  have hne : ∀ g : GL n k, χ g ≠ 0 := by
    intro g h0
    have : χ (g * g⁻¹) = 1 := by simp
    rw [map_mul, h0, zero_mul] at this
    exact zero_ne_one this
  have hdiag : ∀ (D : n → k) (g : GL n k), g.val = diagonal D → χ g = 1 := by
    intro D g hg
    have h1 : χ g⁻¹ = χ g := by
      apply h
      rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hg, diagonal_transpose]
    have h2 : χ g * χ g = 1 := by
      calc χ g * χ g = χ g * χ g⁻¹ := by rw [h1]
        _ = 1 := by rw [← map_mul]; simp
    have h3 : χ g ^ 2 = 1 := by rw [sq, h2]
    exact (pow_eq_one_iff_of_nonneg (zero_le) two_ne_zero).1 h3
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have ha0 : a ≠ 0 := by intro h0; apply ha; simp [h0]
  have ha1 : 1 - a ≠ 0 := by
    intro h0; apply ha; have : a = 1 := by linear_combination -h0
    simp [this]
  have htr : ∀ (t : TransvectionStruct n k) (g : GL n k), g.val = t.toMatrix → χ g = 1 := by
    rintro ⟨i, j, hij, x⟩ g hg
    let T : k → GL n k := fun y => GeneralLinearGroup.mkOfDetNeZero (transvection i j y)
      (by rw [det_transvection_of_ne i j hij]; exact one_ne_zero)
    have hT : ∀ y, (T y).val = transvection i j y := fun y => rfl
    have hgT : g = T x := Units.ext (by rw [hg, hT]; rfl)
    have hconj : ∀ b : k, b ≠ 0 → χ (T (b * x)) = χ (T x) := by
      intro b hb
      let D : GL n k := GeneralLinearGroup.mkOfDetNeZero (diagonal (Function.update 1 i b))
        (by
          rw [det_diagonal]
          refine Finset.prod_ne_zero_iff.2 fun l _ => ?_
          by_cases hl : l = i
          · subst hl; simpa using hb
          · simp [Function.update_of_ne hl])
      have hD : D.val = diagonal (Function.update 1 i b) := rfl
      have e : D * T x = T (b * x) * D := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hD, hT, hT]
        ext p q
        rw [diagonal_mul, mul_diagonal]
        simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
        by_cases hp : i = p
        · subst hp
          by_cases hq : j = q
          · subst hq
            simp [hij, Function.update_of_ne hij.symm]
          · by_cases hpq : i = q
            · subst hpq; simp [hq]
            · simp [hq, hpq]
        · by_cases hpq : p = q
          · subst hpq; simp [hp]
          · simp [hp, hpq]
      have := congrArg χ e
      rw [map_mul, map_mul, hdiag _ D hD, one_mul, mul_one] at this
      exact this.symm
    have e : T x = T (a * x) * T ((1 - a) * x) := by
      apply Units.ext
      rw [Units.val_mul, hT, hT, hT, transvection_mul_transvection_same i j hij]
      congr 1
      ring
    have e2 := congrArg χ e
    rw [map_mul, hconj a ha0, hconj _ ha1] at e2
    rw [hgT]
    exact (mul_eq_left₀ (hne _)).1 e2.symm
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL n k, g.val = M → χ g = 1) g.val g.det_ne_zero
    (fun D _ => hdiag D) htr ?_ g rfl
  intro A B hA hB pA pB u hu
  have : u = GeneralLinearGroup.mkOfDetNeZero A hA * GeneralLinearGroup.mkOfDetNeZero B hB :=
    Units.ext hu
  rw [this, map_mul, pA _ rfl, pB _ rfl, one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantCosetInd
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

noncomputable section

namespace GlobalTheory.InvBilinTest

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

open Classical in

def cosetInd (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (g : G) :
    SB G :=
  ⟨fun x => if x * g⁻¹ ∈ K then 1 else 0, by
    constructor
    · have h1 : IsOpen {x : G | x * g⁻¹ ∈ K} := ho.preimage (continuous_id.mul continuous_const)
      have h2 : IsClosed {x : G | x * g⁻¹ ∈ K} :=
        (K.isClosed_of_isOpen ho).preimage (continuous_id.mul continuous_const)
      rw [IsLocallyConstant.iff_exists_open]
      intro y
      by_cases hy : y * g⁻¹ ∈ K
      · exact ⟨_, h1, hy, fun x hx => by rw [if_pos hy]; exact if_pos hx⟩
      · exact ⟨_, h2.isOpen_compl, hy, fun x hx => by rw [if_neg hy]; exact if_neg hx⟩
    · refine HasCompactSupport.intro (hK.image (continuous_id.mul (continuous_const (y := g))))
        fun x hx => if_neg fun h => hx ⟨_, h, by simp⟩⟩

open Classical in

theorem cosetInd_apply (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    (g x : G) : (cosetInd K ho hK g).1 x = if x * g⁻¹ ∈ K then 1 else 0 := rfl

theorem isLocallyConstant_cosetInd (K : Subgroup G) (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) : IsLocallyConstant (cosetInd K ho hK) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨{h | g * h⁻¹ ∈ K}, ho.preimage (continuous_const.mul continuous_inv), by simp,
    fun h hh => Subtype.ext (funext fun x => ?_)⟩
  rw [cosetInd_apply, cosetInd_apply]
  have : x * h⁻¹ = x * g⁻¹ * (g * h⁻¹) := by group
  classical
  have hh' : g * h⁻¹ ∈ K := hh
  rw [this]
  exact if_congr (K.mul_mem_cancel_right hh') rfl rfl

variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]

open MeasureTheory in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] in
variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y] in
omit [T2Space G] in
open Classical in

theorem _root_.GlobalTheory.InvBilinTest.integral_ite (K : Subgroup G) (ho : IsOpen (K : Set G)) (c : ℂ) :
    ∫ g, (if g ∈ K then c else 0) ∂μ = (μ.real K : ℂ) * c := by
  have hm : MeasurableSet (K : Set G) := ho.measurableSet
  have h : (fun g : G => if g ∈ K then c else 0) = (K : Set G).indicator (fun _ => c) := by
    ext g
    simp [Set.indicator_apply]
  rw [h, integral_indicator_const c hm, Complex.real_smul]

theorem smoothOp_cosetInd (hπ : IsSmooth π) (K : Subgroup G) (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) {w : V} (hw : ∀ k ∈ K, π k w = w) :
    smoothOp π μ (cosetInd K ho hK 1).1 w = (μ.real K : ℂ) • w := by
  refine eq_of_forall_dual fun l => ?_
  rw [hπ.map_smoothOp (cosetInd K ho hK 1).2.1 (cosetInd K ho hK 1).2.2, map_smul, smul_eq_mul,
    ← integral_ite K ho]
  congr 1
  ext g
  rw [cosetInd_apply]
  by_cases hg : g ∈ K
  · simp [hg, hw g hg]
  · simp [hg]

theorem key [μ.IsMulRightInvariant] (hπ : IsSmooth π) (B : SB G →ₗ[ℂ] V →ₗ[ℂ] Y)
    (hB : ∀ (g : G) (φ ψ : SB G) (v : V), (∀ x, ψ.1 x = φ.1 (x * g)) → B ψ (π g v) = B φ v)
    (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    (φ : SB G) (hφ : ∀ k ∈ K, ∀ g, φ.1 (k * g) = φ.1 g) (v : V) :
    B (cosetInd K ho hK 1) (smoothOp π μ φ.1 v) = (μ.real K : ℂ) • B φ v := by
  classical
  have hF : IsLocallyConstant fun g => φ.1 g • cosetInd K ho hK g :=
    φ.2.1.comp₂ (isLocallyConstant_cosetInd K ho hK) (· • ·)
  have hc : HasCompactSupport fun g => φ.1 g • cosetInd K ho hK g :=
    HasCompactSupport.intro φ.2.2 fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have h1 : lcIntegral μ (fun g => φ.1 g • cosetInd K ho hK g) = (μ.real K : ℂ) • φ := by
    refine Subtype.ext (funext fun x => ?_)
    have := map_lcIntegral (μ := μ) hF hc (LinearMap.proj (R := ℂ) (φ := fun _ : G => ℂ) x ∘ₗ (SB G).subtype)
    refine this.trans ?_
    show ∫ g, φ.1 g * (cosetInd K ho hK g).1 x ∂μ = (μ.real K : ℂ) * φ.1 x
    rw [← integral_ite K ho, ← integral_mul_right_eq_self _ x]
    congr 1
    ext g
    rw [cosetInd_apply]
    by_cases hg : g ∈ K
    · simp [hg, hφ g hg]
    · simp [hg]
  refine eq_of_forall_dual fun l => ?_
  have h2 := map_lcIntegral (μ := μ) hF hc (l ∘ₗ B.flip v)
  have h3 := hπ.map_smoothOp (μ := μ) φ.2.1 φ.2.2 (l ∘ₗ B (cosetInd K ho hK 1)) v
  rw [h1] at h2
  simp only [LinearMap.comp_apply, map_smul, LinearMap.flip_apply] at h2 h3 ⊢
  rw [h2, h3]
  congr 1
  ext g
  rw [hB g (cosetInd K ho hK g) (cosetInd K ho hK 1) v fun x => by simp [cosetInd_apply]]

theorem exists_factor (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G,
      IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hπ : IsSmooth π)
    (Y : Type) [AddCommGroup Y] [Module ℂ Y] (B : SB G →ₗ[ℂ] V →ₗ[ℂ] Y)
    (hB : ∀ (g : G) (φ ψ : SB G) (v : V), (∀ x, ψ.1 x = φ.1 (x * g)) → B ψ (π g v) = B φ v) :
    ∃ B₀ : V →ₗ[ℂ] Y, ∀ (φ : SB G) (v : V), B φ v = B₀ (smoothOp π μ φ.1 v) := by
  have hpos : ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
      (μ.real K : ℂ) ≠ 0 := fun K ho hK => by
    have h1 : μ K ≠ 0 := (ho.measure_pos μ ⟨1, K.one_mem⟩).ne'
    have h2 : μ.real K ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h1, hK.measure_ne_top⟩
    exact_mod_cast h2
  have hle : ∀ (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
      (L : Subgroup G) (ho' : IsOpen (L : Set G)) (hL : IsCompact (L : Set G)), L ≤ K →
      ∀ w, (∀ k ∈ K, π k w = w) →
      (μ.real K : ℂ)⁻¹ • B (cosetInd K ho hK 1) w = (μ.real L : ℂ)⁻¹ • B (cosetInd L ho' hL 1) w := by
    intro K ho hK L ho' hL hLK w hw
    have h := key (μ := μ) hπ B hB L ho' hL (cosetInd K ho hK 1) (fun k hk g => by
      classical
      rw [cosetInd_apply, cosetInd_apply, mul_assoc]
      exact if_congr (K.mul_mem_cancel_left (hLK hk)) rfl rfl) w
    rw [smoothOp_cosetInd hπ K ho hK hw, map_smul] at h
    rw [inv_smul_eq_iff₀ (hpos K ho hK), smul_comm, h, inv_smul_smul₀ (hpos L ho' hL)]
  have hex : ∀ w : V, ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧
      ∀ k ∈ K, π k w = w := fun w => by
    obtain ⟨K, ho, hK, h⟩ := hG _ ((hπ w).mem_nhds (show π 1 w = w by simp))
    exact ⟨K, ho, hK, fun k hk => h hk⟩
  choose K ho hK hw using hex
  have hinter : ∀ (L M : Subgroup G), IsCompact (L : Set G) → IsOpen (M : Set G) →
      IsCompact ((L ⊓ M : Subgroup G) : Set G) := fun L M hL hM =>
    hL.inter_right (M.isClosed_of_isOpen hM)
  let b : V → Y := fun w => (μ.real (K w) : ℂ)⁻¹ • B (cosetInd (K w) (ho w) (hK w) 1) w
  have hb : ∀ (L : Subgroup G) (ho' : IsOpen (L : Set G)) (hL : IsCompact (L : Set G)) (w : V),
      (∀ k ∈ L, π k w = w) → b w = (μ.real L : ℂ)⁻¹ • B (cosetInd L ho' hL 1) w := by
    intro L ho' hL w h
    have h1 : IsOpen ((L ⊓ K w : Subgroup G) : Set G) := ho'.inter (ho w)
    have h2 := hinter L (K w) hL (ho w)
    exact (hle _ _ _ _ h1 h2 inf_le_right w (hw w)).trans (hle _ _ _ _ h1 h2 inf_le_left w h).symm
  refine ⟨⟨⟨b, fun v w => ?_⟩, fun c v => ?_⟩, fun φ v => ?_⟩
  · have h1 : IsOpen ((K v ⊓ K w : Subgroup G) : Set G) := (ho v).inter (ho w)
    have h2 := hinter (K v) (K w) (hK v) (ho w)
    rw [hb _ h1 h2 v fun k hk => hw v k hk.1, hb _ h1 h2 w fun k hk => hw w k hk.2,
      hb _ h1 h2 (v + w) fun k hk => by rw [map_add, hw v k hk.1, hw w k hk.2], map_add, smul_add]
  · show b (c • v) = c • b v
    rw [hb _ (ho v) (hK v) (c • v) fun k hk => by rw [map_smul, hw v k hk], map_smul, smul_comm]
  · show _ = b _
    obtain ⟨L, ho', hL, h⟩ := hG _ ((isOpen_leftStabilizer φ.2.1 φ.2.2).mem_nhds (one_mem _))
    have hφ : ∀ k ∈ L, ∀ g, φ.1 (k * g) = φ.1 g := fun k hk => h hk
    rw [hb L ho' hL _ (mem_fixed.1 (hπ.smoothOp_mem_fixed φ.2.1 φ.2.2 hφ v)),
      key hπ B hB L ho' hL φ hφ, inv_smul_smul₀ (hpos L ho' hL)]

end GlobalTheory.InvBilinTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker

namespace GlobalTheory.SplitWeil

theorem map_curry_symm_pi_pi {X a b : Type} [MeasurableSpace X] [Fintype a] [Fintype b] (ν : Measure X)
    [SigmaFinite ν] :
    Measure.map (MeasurableEquiv.curry b a X).symm (Measure.pi fun _ : b => Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : b × a => ν := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.curry b a X).symm.measurable (MeasurableSet.univ_pi hs)]
  have hpre : (MeasurableEquiv.curry b a X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : b => Set.univ.pi fun j : a => s (i, j) := by
    ext x
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]

omit [MeasurableSpace k] [BorelSpace k] in
theorem nabs_pos' (x : kˣ) : 0 < nabs k x := by
  show (0 : ℝ) < ((distribHaarChar k x : NNReal) : ℝ)
  exact NNReal.coe_pos.mpr distribHaarChar_pos

private lemma measurable_mulVec' {ι : Type} [Fintype ι] (M : Matrix ι ι k) : Measurable M.mulVec := by
  have : SecondCountableTopology k := secondCountable k
  exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable

private lemma map_diagonal_mulVec_measure_pi (D : a → k) (u : kˣ) (hu : (u : k) = (Matrix.diagonal D).det) :
    Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    have h0 : (u : k) ≠ 0 := u.ne_zero
    rw [hu, Matrix.det_diagonal] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  let e : a → kˣ := fun i => Units.mk0 (D i) (hD i)
  have hue : u = ∏ i, e i := by
    ext
    rw [hu, Matrix.det_diagonal, Units.coe_prod]
    rfl
  have hm := measurable_mulVec' (Matrix.diagonal D)
  have E : distribHaarChar k u • Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : a => ν := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.smul_apply, Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have hpre : (Matrix.diagonal D).mulVec ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => (fun x : k => e i • x) ⁻¹' s i := by
      ext x
      simp [Matrix.mulVec_diagonal, Units.smul_def, e]
    rw [hpre, Measure.pi_pi, hue, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Set.preimage_smul, ← distribHaarChar_mul ν (e i)⁻¹, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel,
      map_one, ENNReal.coe_one, one_mul]
  calc Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν)
      = (distribHaarChar k u⁻¹ * distribHaarChar k u) •
          Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) := by
        rw [← map_mul, inv_mul_cancel, map_one, one_smul]
    _ = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by rw [mul_smul, E]

private lemma map_transvection_mulVec_measure_pi (t : Matrix.TransvectionStruct a k) :
    Measure.map t.toMatrix.mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  obtain ⟨i, j, hij, c⟩ := t
  show Measure.map (Matrix.transvection i j c).mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν
  have hm := measurable_mulVec' (Matrix.transvection i j c)
  have key : ∀ (x : a → k) (y : k), (Matrix.transvection i j c).mulVec (Function.update x i y) =
      Function.update x i (y + c * x j) := by
    intro x y
    ext l
    by_cases hl : l = i
    · subst hl
      simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hij.symm]
    · simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hl, Ne.symm hl]
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hind : Measurable ((Set.univ.pi s).indicator (1 : (a → k) → ENNReal)) := measurable_one.indicator hbox
  rw [← Measure.pi_pi, ← lintegral_indicator_one hbox, ← lintegral_indicator_one hbox,
    lintegral_map hind hm]
  refine lintegral_eq_of_lmarginal_eq {i} (hind.comp hm) hind ?_
  ext x
  rw [lmarginal_singleton, lmarginal_singleton]
  simp only [Function.comp_apply, key]
  exact lintegral_add_right_eq_self (fun y => (Set.univ.pi s).indicator 1 (Function.update x i y)) (c * x j)

private lemma map_mulVec_measure_pi_eq_distribHaarChar_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det) :
    Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  revert u
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : kˣ, (u : k) = M.det →
      Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν)
    M hM ?_ ?_ ?_
  · intro D _ u hu
    exact map_diagonal_mulVec_measure_pi ν D u hu
  · intro t u hu
    have h1 : u = 1 := Units.ext (by rw [hu, Matrix.TransvectionStruct.det, Units.val_one])
    rw [h1, inv_one, map_one, one_smul, map_transvection_mulVec_measure_pi ν t]
  · intro A B hA hB IA IB u hu
    have hfun : (A * B).mulVec = A.mulVec ∘ B.mulVec := by
      funext x
      simp [Matrix.mulVec_mulVec]
    have hinv : u⁻¹ = (Units.mk0 _ hB)⁻¹ * (Units.mk0 _ hA)⁻¹ := by
      rw [← mul_inv]
      congr 1
      ext
      simp [hu, Matrix.det_mul, mul_comm]
    rw [hfun, ← Measure.map_map (measurable_mulVec' A) (measurable_mulVec' B), IB (Units.mk0 _ hB) rfl,
      Measure.map_smul, IA (Units.mk0 _ hA) rfl, hinv, map_mul, mul_smul]

private lemma integral_comp_mulVec_eq_nabs_inv_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det)
    (f : (a → k) → ℂ) :
    ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ((nabs k u)⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ : a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  let e : (a → k) ≃ᵐ (a → k) :=
    { toFun := M.mulVec
      invFun := M⁻¹.mulVec
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet]
      measurable_toFun := measurable_mulVec' M
      measurable_invFun := measurable_mulVec' M⁻¹ }
  have h1 : ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ∫ y, f y ∂(Measure.map e (Measure.pi fun _ : a => ν)) := (e.measurableEmbedding.integral_map f).symm
  have h2 : (e : (a → k) → (a → k)) = M.mulVec := rfl
  rw [h1, h2, map_mulVec_measure_pi_eq_distribHaarChar_smul ν hM u hu, integral_smul_nnreal_measure, map_inv, NNReal.smul_def,
    NNReal.coe_inv]
  rfl

theorem integral_comp_mulVec_eq_smul (g : GL a k) (f : (a → k) → ℂ) :
    ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) =
      ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν) := by
  exact integral_comp_mulVec_eq_nabs_inv_smul ν (Matrix.GeneralLinearGroup.det g).ne_zero _ rfl f

omit [BorelSpace k] [DecidableEq a] [DecidableEq b] in
theorem integral_volM_eq_pi (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ x ∂(volM ν b a) = ∫ y, Φ (Matrix.of (Function.curry y)) ∂(Measure.pi fun _ : b × a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  rw [← map_curry_symm_pi_pi ν, (MeasurableEquiv.curry b a k).symm.measurableEmbedding.integral_map]
  rfl

private lemma mul_of_curry_mul_eq_of_curry_kronecker_mulVec (g : GL a k) (h : GL b k) (y : b × a → k) :
    h.val * Matrix.of (Function.curry y) * g.val =
      Matrix.of (Function.curry ((h.val ⊗ₖ g.valᵀ).mulVec y)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Function.curry_apply, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem integral_comp_mul_mul_volM (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) =
      (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) *
        nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  have hK : (h.val ⊗ₖ g.valᵀ).det ≠ 0 := by
    rw [Matrix.det_kronecker, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (Matrix.GeneralLinearGroup.det h).ne_zero)
      (pow_ne_zero _ (Matrix.GeneralLinearGroup.det g).ne_zero)
  set u : kˣ := Matrix.GeneralLinearGroup.det h ^ Fintype.card a *
    Matrix.GeneralLinearGroup.det g ^ Fintype.card b with hu_def
  have hu : (u : k) = (h.val ⊗ₖ g.valᵀ).det := by
    rw [Matrix.det_kronecker, Matrix.det_transpose, hu_def, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val]
    rfl
  rw [integral_volM_eq_pi ν (fun x => Φ (h.val * x * g.val)), integral_volM_eq_pi ν Φ]
  simp only [mul_of_curry_mul_eq_of_curry_kronecker_mulVec g h]
  rw [integral_comp_mulVec_eq_nabs_inv_smul ν hK u hu (fun y => Φ (Matrix.of (Function.curry y)))]
  congr 1
  have hn : nabs k u = nabs k (Matrix.GeneralLinearGroup.det h) ^ Fintype.card a *
      nabs k (Matrix.GeneralLinearGroup.det g) ^ Fintype.card b := by
    simp only [nabs, hu_def, map_mul, map_pow, NNReal.coe_mul, NNReal.coe_pow]
  rw [hn, mul_inv, Real.rpow_neg (nabs_pos' _).le, Real.rpow_neg (nabs_pos' _).le, Real.rpow_natCast,
    Real.rpow_natCast]

theorem linear_change_of_variables : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure], (∀ (g : GL a k) (f : (a → k) → ℂ), ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) = ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν)) ∧ ∀ (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) = (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  intro k _ _ _ _ _ _ a b _ _ _ _ ν _
  exact ⟨fun g f => integral_comp_mulVec_eq_smul ν g f, fun g h Φ => integral_comp_mul_mul_volM ν g h Φ⟩

end GlobalTheory.SplitWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearZeroOfKillsTranslatesTensorStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinear_zero_of_kills_translates_tensor : ∀ (ι : Type) [Fintype ι] (H : ι → Type) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)] (G : ι → Type) [∀ i, Group (G i)] (π : ∀ i, G i →* (H i →L[ℂ] H i)), (∀ i g x, ‖π i g x‖ = ‖x‖) → (∀ i, ∀ B : H i →L[ℂ] H i, (∀ g, B.comp (π i g) = (π i g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ (H i)) → ∀ (Sm : ∀ i, Submodule ℂ (H i)), (∀ i, Dense (Sm i : Set (H i))) → ∀ (hinv : ∀ i g, ∀ x ∈ Sm i, π i g x ∈ Sm i) (L : MultilinearMap ℂ (fun i => Sm i) ℂ) (C : ℝ), (∀ v, ‖L v‖ ≤ C * ∏ i, ‖(v i : H i)‖) → ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → ∀ i, Sm i), (∀ g : ∀ i, G i, ∑ j, c j * L (fun i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩) = 0) → ∀ (φ : ∀ i, H i) (u : ∀ i, Sm i), (∑ j, c j * ∏ i, ⟪φ i, (v j i : H i)⟫_ℂ) * L u = 0 := by
  first | exact @GlobalTheory.DensityMultiPlace.multilinear_translates_zero | exact GlobalTheory.DensityMultiPlace.multilinear_translates_zero | (intros; apply GlobalTheory.DensityMultiPlace.multilinear_translates_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodicThetaNormMeanFactorLeStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_theta_norm_mean_factor_le : ∀ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (p n : ℕ) (v : Fin n → (Fin g → ℂ)) (T : ℝ), Countable Λ → Countable Λ' → MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume → 0 < p → (∀ a ∈ Λ, h a ∈ Λ') → (∀ z, 0 ≤ u z) → (∀ z, 0 ≤ u' z) → (∀ a ∈ Λ, ∀ z, u (z + a) = u z) → (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) → (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 → (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 → (∀ z, T * u' (h z) ≤ ∑ m, u ((p : ℂ) • z + v m)) → T ≤ n := by
  first | exact @GlobalTheory.PeriodicMean.mean_factor_le | exact GlobalTheory.PeriodicMean.mean_factor_le | (intros; apply GlobalTheory.PeriodicMean.mean_factor_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightConvEqSmulOfInnerTranslatesStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightConv_eq_smul_of_inner_translates_eq : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ {H : Subgroup G} (m : Measure H) [SFinite m] (α : H → ℂ), Integrable α m → ∀ (φ : G → ℂ), Continuous φ → ∀ B : ℝ, (∀ g, ‖φ g‖ ≤ B) → (∀ γ ∈ Γ, ∀ x, φ (γ * x) = φ x) → ∀ c : ℂ, (∀ h' : H, ∫ x in 𝓕, star (φ (x * (h' : G))) * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ = c * ∫ x in 𝓕, star (φ (x * (h' : G))) * φ x ∂μ) → ∀ x, ∫ h, α h * φ (x * (h : G)) ∂m = c * φ x := by
  first | exact @GlobalTheory.rightConv_eq_smul_of_inner_translates | exact GlobalTheory.rightConv_eq_smul_of_inner_translates | (intros; apply GlobalTheory.rightConv_eq_smul_of_inner_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelationStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchange_support_and_fourier_relation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (IsNEquiv ψ p σ l → (fun u : n → k => l (σ (rowE c p u) v)) ∈ SB (n → k) ∧ (∀ u β : n → k, l (σ (rowE c p u) (σ (colE c (p + 1) β) v)) = (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v)) ∧ ∀ β : n → k, exUp ν p σ l (σ (colE c (p + 1) β) v) = ∫ u : n → k, (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν)) ∧ (IsNEquiv ψ (p + 1) σ l → (fun β : n → k => l (σ (colE c (p + 1) β) v)) ∈ SB (n → k) ∧ ∀ u β : n → k, l (σ (colE c (p + 1) β) (σ (rowE c p u) v)) = (ψ (-(u ⬝ᵥ β)) : ℂ) * l (σ (colE c (p + 1) β) v)) := by
  first | exact @GlobalTheory.RootEx.ExchangeSupport.exchange_support | exact GlobalTheory.RootEx.ExchangeSupport.exchange_support | (intros; apply GlobalTheory.RootEx.ExchangeSupport.exchange_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvariaStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_matrix_exists_open_addSubgroup_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [Fintype b], ∀ Φ ∈ SB (Matrix a b k), ∃ Λ : AddSubgroup (Matrix a b k), IsOpen (Λ : Set (Matrix a b k)) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  first | exact @GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup | exact GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup | (intros; apply GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryCharacterKillsUnitaryTransvectionsStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCharacter_kills_unitaryTransvections : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ m ∈ GlobalTheory.UTrans.TvGen σ G, X m = 1 := by
  first | exact @GlobalTheory.UTrans.TvKill.char_tvGen | exact GlobalTheory.UTrans.TvKill.char_tvGen | (intros; apply GlobalTheory.UTrans.TvKill.char_tvGen <;> assumption)
end

