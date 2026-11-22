import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0065
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeEqFiniteTranslateCombOfLevelStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exchange_eq_finiteTranslateComb_of_level : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (U : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (U : Set (GL (n ⊕ Fin c) k))), ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ, ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (∀ u ∈ U, σ u v = v) → (IsNEquiv ψ (p + 1) σ l → exDown ν p σ l v = comb e fun g => l (σ g v)) ∧ (IsNEquiv ψ p σ l → exUp ν p σ l v = comb e' fun g => l (σ g v)) := by
  first | exact @GlobalTheory.PosOne.exchange_eq_comb | exact GlobalTheory.PosOne.exchange_eq_comb | (intros; apply GlobalTheory.PosOne.exchange_eq_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEqAdicCompletionIntegersStatement
section
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_binary_quadratic_eq_unit_of_disc_isUnit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  first | exact @GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | exact GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | (intros; apply GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnSupportOfOneIndexAtSymPositionStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatColumnSupport_of_oneIndexAt_symPosition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneIndexAt t ν → GlobalTheory.LocFlat.SuppCol S t ν := by
  first | exact @GlobalTheory.LocFlat.suppCol_of_oneIndexAt | exact GlobalTheory.LocFlat.suppCol_of_oneIndexAt | (intros; apply GlobalTheory.LocFlat.suppCol_of_oneIndexAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowIndicatorOfSymLevelExchangeStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatRowIndicator_of_symLevelExchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureRow S t ν := by
  first | exact @GlobalTheory.LocFlat.pureRow_of_exchange | exact GlobalTheory.LocFlat.pureRow_of_exchange | (intros; apply GlobalTheory.LocFlat.pureRow_of_exchange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeSeriesCellHasSum
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.LatticePair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def IsInt (A : GL (Fin n) k) : Prop := ∀ i j, A.1 i j ∈ 𝒪[k]

theorem isInt_mul {A B : GL (Fin n) k} (hA : IsInt A) (hB : IsInt B) : IsInt (A * B) := fun i j => by
  rw [Units.val_mul, Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem isInt_mul_KO_iff {A κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) : IsInt (A * κ) ↔ IsInt A := by
  have h := (SplitFlip.mem_KO_iff κ).1 hκ
  refine ⟨fun hA => ?_, fun hA => isInt_mul hA h.1⟩
  have := isInt_mul hA h.2
  rwa [mul_inv_cancel_right] at this

theorem isInt_KO_mul_iff {A κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) : IsInt (κ * A) ↔ IsInt A := by
  have h := (SplitFlip.mem_KO_iff κ).1 hκ
  refine ⟨fun hA => ?_, fun hA => isInt_mul h.1 hA⟩
  have := isInt_mul h.2 hA
  rwa [inv_mul_cancel_left] at this

theorem ord_det_of_mem_KO {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det κ) = 0 := by
  obtain ⟨u, rfl⟩ := hκ
  apply ord_eq_zero
  have h1 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) =
      algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det u : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem ord_det_mul (a b : GL (Fin n) k) : ord k (Matrix.GeneralLinearGroup.det (a * b)) =
    ord k (Matrix.GeneralLinearGroup.det a) + ord k (Matrix.GeneralLinearGroup.det b) := by
  rw [map_mul, ord_mul]

theorem ord_det_inv (a : GL (Fin n) k) : ord k (Matrix.GeneralLinearGroup.det a⁻¹) =
    -ord k (Matrix.GeneralLinearGroup.det a) := by
  have := ord_det_mul a a⁻¹
  rw [mul_inv_cancel, map_one, ord_eq_zero (by simp)] at this
  omega

theorem valuation_det_le_one {A : GL (Fin n) k} (hA : IsInt A) :
    valuation k ((Matrix.GeneralLinearGroup.det A : kˣ) : k) ≤ 1 := by
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨A.1 i j, hA i j⟩
  have hB : (algebraMap 𝒪[k] k).mapMatrix B = A.1 := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← hB, ← RingHom.map_det]
  exact B.det.2

theorem ord_nonneg_of_le_one {x : kˣ} (hx : valuation k (x : k) ≤ 1) : 0 ≤ ord k x := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (x : k)) ≠ 0 := by simp
  have h1 : φ (valuation k (x : k)) ≤ φ 1 := φ.strictMono.monotone hx
  rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  show 0 ≤ -WithZero.log (φ (valuation k (x : k)))
  omega

theorem ord_det_torusElt {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin n → ℤ) :
    ord k (Matrix.GeneralLinearGroup.det (torusElt k (Fin n) ϖ e)) = ∑ i, e i := by
  have h1 : Matrix.GeneralLinearGroup.det (torusElt k (Fin n) ϖ e) = ϖ ^ ∑ i, e i := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, val_torusElt, Matrix.det_diagonal, Units.val_zpow_eq_zpow_val]
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have := map_zpow o ϖ (∑ i, e i)
  rw [show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd (ord_eq_one hϖ), ← ofAdd_zsmul,
    smul_eq_mul, mul_one, ← h1] at this
  exact this

theorem isInt_and_mul_torus_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (A : GL (Fin n) k)
    (e : Fin n → ℤ) : IsInt A ∧ IsInt (A * torusElt k (Fin n) ϖ e) ↔
      IsInt (A * torusElt k (Fin n) ϖ fun i => min (e i) 0) := by
  have hle : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  have hpow : ∀ m : ℤ, 0 ≤ m → (ϖ : k) ^ m ∈ 𝒪[k] := fun m hm => by
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [zpow_natCast]
    exact pow_mem hle m
  have hent : ∀ (f : Fin n → ℤ) i j, (A * torusElt k (Fin n) ϖ f).1 i j = A.1 i j * (ϖ : k) ^ f j :=
    fun f i j => by rw [Units.val_mul, val_torusElt, Matrix.mul_diagonal]
  have key : ∀ (x : k) (m : ℤ), (x ∈ 𝒪[k] ∧ x * (ϖ : k) ^ m ∈ 𝒪[k]) ↔ x * (ϖ : k) ^ min m 0 ∈ 𝒪[k] := by
    intro x m
    have hz : (ϖ : k) ≠ 0 := ϖ.ne_zero
    rcases le_total m 0 with h | h
    · rw [min_eq_left h]
      refine ⟨And.right, fun h2 => ⟨?_, h2⟩⟩
      have : x = x * (ϖ : k) ^ m * (ϖ : k) ^ (-m) := by
        rw [mul_assoc, ← zpow_add₀ hz, add_neg_cancel, zpow_zero, mul_one]
      rw [this]
      exact mul_mem h2 (hpow _ (by omega))
    · rw [min_eq_right h, zpow_zero, mul_one]
      exact ⟨And.left, fun h2 => ⟨h2, mul_mem h2 (hpow _ h)⟩⟩
  simp only [IsInt, hent]
  constructor
  · rintro ⟨h1, h2⟩ i j
    exact (key _ _).1 ⟨h1 i j, h2 i j⟩
  · intro h
    exact ⟨fun i j => ((key _ _).2 (h i j)).1, fun i j => ((key _ _).2 (h i j)).2⟩

theorem out_eq_mul {r : GL (Fin n) k} {c : GL (Fin n) k ⧸ KO k (Fin n)}
    (h : (r : GL (Fin n) k ⧸ KO k (Fin n)) = c) : ∃ κ ∈ KO k (Fin n), c.out = r * κ := by
  subst h
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) r
  exact ⟨κ, κ.2, hκ⟩

theorem smul_out (u : GL (Fin n) k) (c : GL (Fin n) k ⧸ KO k (Fin n)) :
    ∃ κ ∈ KO k (Fin n), (u • c).out = u * c.out * κ := by
  apply out_eq_mul
  conv_rhs => rw [← QuotientGroup.out_eq' c]
  rfl

theorem hasSum_pair (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin n → ℤ) (g : GL (Fin n) k)
    (hg : g ∈ cell k (Fin n) ϖ e) (X : ℂ) (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) :
    HasSum (fun h : {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
        (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.1.out)).toNat +
        (ord k (Matrix.GeneralLinearGroup.det (h.1.out⁻¹ * g))).toNat))
      (X ^ (∑ i, |e i|).toNat * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) := by
  obtain ⟨x, hx, y, hy, hgxy⟩ := DoubleCoset.mem_doubleCoset.1 hg
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) k, u = x * torusElt k (Fin n) ϖ fun i => min (e i) 0 := ⟨_, rfl⟩
  have hP : ∀ h : GL (Fin n) k, (IsInt h⁻¹ ∧ IsInt (h⁻¹ * g)) ↔ IsInt (h⁻¹ * u) := fun h => by
    rw [hgxy, hu, ← mul_assoc, ← mul_assoc, ← mul_assoc, isInt_mul_KO_iff hy, ← isInt_and_mul_torus_iff hϖ,
      isInt_mul_KO_iff hx]
  let E : {c : GL (Fin n) k ⧸ KO k (Fin n) // ∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]} ≃
      {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
        (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} :=
    (MulAction.toPerm u).subtypeEquiv fun c => by
      obtain ⟨κ, hκ, h⟩ := smul_out u c
      refine Iff.trans ?_ (hP (u • c).out).symm
      have : (u * c.out * κ)⁻¹ * u = κ⁻¹ * c.out⁻¹ := by group
      rw [h, this, isInt_KO_mul_iff (inv_mem hκ)]
      rfl
  have hN := (GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse k n (fun _ => 1) (fun _ => 1) (isBorelSph_one k) (fun _ => one_ne_zero) (X ^ 2)
    fun i => by simpa only [inv_one, mul_one] using hX i).mul_left (X ^ (∑ i, |e i|).toNat)
  simp only [inv_one, mul_one] at hN
  rw [← E.hasSum_iff]
  refine (congrArg (HasSum · _) (funext fun c => ?_)).mpr hN
  obtain ⟨κ, hκ, h⟩ := smul_out u c.1
  have hE : (E c).1.out = u * c.1.out * κ := h
  have hj := ord_nonneg_of_le_one (valuation_det_le_one (A := c.1.out⁻¹) c.2)
  have habs : ∑ i, |e i| = ∑ i, e i - 2 * ∑ i, min (e i) 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_eq_max_neg]
    omega
  have h1 : ∑ i, min (e i) 0 ≤ 0 := Finset.sum_nonpos fun i _ => min_le_right _ _
  have h2 : ∑ i, min (e i) 0 ≤ ∑ i, e i := Finset.sum_le_sum fun i _ => min_le_left _ _
  have hou : ord k (Matrix.GeneralLinearGroup.det u) = ∑ i, min (e i) 0 := by
    rw [hu, ord_det_mul, ord_det_of_mem_KO hx, ord_det_torusElt hϖ, zero_add]
  have hog : ord k (Matrix.GeneralLinearGroup.det g) = ∑ i, e i := by
    rw [hgxy, ord_det_mul, ord_det_mul, ord_det_of_mem_KO hx, ord_det_of_mem_KO hy, ord_det_torusElt hϖ,
      zero_add, add_zero]
  rw [ord_det_inv] at hj
  simp only [Function.comp_apply]
  rw [ord_det_mul, ord_det_inv, hE, ord_det_mul, ord_det_mul, ord_det_of_mem_KO hκ, hou, hog,
    ← pow_mul, ← pow_add, habs]
  congr 1
  omega

end GlobalTheory.LatticePair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.LocFlat.CFac

theorem coe_psi_mul_neg {k : Type} [AddGroup k] (ψ : AddChar k Circle) (a : k) : (ψ a : ℂ) * ψ (-a) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

theorem coe_psi_add {k : Type} [AddGroup k] (ψ : AddChar k Circle) (a b : k) : (ψ (a + b) : ℂ) = ψ a * ψ b := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

end GlobalTheory.LocFlat.CFac

namespace GlobalTheory.LocFlat
open GlobalTheory.LocFlat.CFac

theorem contrFactor : ContrFactor := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν n n' n'' _ _ _ _ _ _ M _ _ B h1 h2
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI hTD : ∀ (a b : Type) [Fintype a] [Fintype b], TotallyDisconnectedSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (TotallyDisconnectedSpace (a → b → k))
  haveI hLC : ∀ (a b : Type) [Fintype a] [Fintype b], LocallyCompactSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (LocallyCompactSpace (a → b → k))
  have hψlc := GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψc
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_linear_of_bilinear_schwartzBruhatProduct _ _ M B

  set X₁ := Matrix n (n' ⊕ Unit) k
  set X₂ := Matrix (n'' ⊕ Unit) n k

  let uy : X₁ × X₂ → k := fun z => z.2 (Sum.inr ()) ⬝ᵥ fun r => z.1 r (Sum.inr ())
  have huy : Continuous uy := by
    refine Continuous.dotProduct ?_ ?_
    · exact continuous_pi fun r => (continuous_apply r).comp ((continuous_apply (Sum.inr ())).comp continuous_snd)
    · exact continuous_pi fun r => (continuous_apply (Sum.inr ())).comp ((continuous_apply r).comp continuous_fst)
  have hχ : IsLocallyConstant fun z => (ψ (-uy z) : ℂ) := hψlc.comp_continuous huy.neg
  have hχi : IsLocallyConstant fun z => (ψ (uy z) : ℂ) := hψlc.comp_continuous huy
  let L : SB (X₁ × X₂) →ₗ[ℂ] M := l ∘ₗ mulLC _ hχi
  have key : ∀ f g, L (mulLC _ hχ (prodSB f g)) = B f g := by
    intro f g
    rw [← hl]
    show l _ = l _
    congr 1
    ext z
    simp only [mulLC_apply, ← mul_assoc, coe_psi_mul_neg, one_mul]
  have hspan : Submodule.span ℂ (Set.range fun q : SB X₁ × SB X₂ => mulLC _ hχ (prodSB q.1 q.2)) = ⊤ := by
    have hsurj : Function.Surjective (mulLC _ hχ) := fun F => ⟨mulLC _ hχi F, by
      ext z; simp only [mulLC_apply, ← mul_assoc]; rw [mul_comm (ψ (-uy z) : ℂ), coe_psi_mul_neg, one_mul]⟩
    rw [Set.range_comp' (mulLC _ hχ) (fun q : SB X₁ × SB X₂ => prodSB q.1 q.2), Submodule.span_image,
      GlobalTheory.T.span_schwartzBruhatProduct_eq_top, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]

  have transY : ∀ y₀ : n → k, L ∘ₗ comapH (Homeomorph.addRight ((fromCols 0 (Matrix.of fun r _ => y₀ r) : X₁), (0 : X₂))) = L := by
    intro y₀
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨⟨f, g⟩, rfl⟩
    have hc : IsLocallyConstant fun x : X₂ => (ψ (-(x (Sum.inr ()) ⬝ᵥ y₀)) : ℂ) :=
      hψlc.comp_continuous (Continuous.neg (Continuous.dotProduct
        (continuous_pi fun r => (continuous_apply r).comp (continuous_apply (Sum.inr ()))) continuous_const))
    set C : X₁ := fromCols 0 (Matrix.of fun r _ => y₀ r)
    let f' := comapH (Homeomorph.addRight C) f
    let g' := mulLC _ hc g
    have hu : ∀ z : X₁ × X₂, uy (z + (C, 0)) = uy z + z.2 (Sum.inr ()) ⬝ᵥ y₀ := by
      intro z
      simp only [uy, Prod.fst_add, Prod.snd_add, add_zero, Matrix.add_apply, C, fromCols_apply_inr, Matrix.of_apply]
      rw [← dotProduct_add]; rfl
    have e1 : comapH (Homeomorph.addRight (C, (0 : X₂))) (mulLC _ hχ (prodSB f g)) = mulLC _ hχ (prodSB f' g') := by
      ext z
      simp only [comapH_apply, mulLC_apply, prodSB_apply, Homeomorph.coe_addRight, f', g']
      rw [hu, neg_add, coe_psi_add]
      simp only [Prod.fst_add, Prod.snd_add, add_zero]
      ring
    rw [LinearMap.comp_apply, e1, key, key]
    exact h2 y₀ f f' g g' (fun x => rfl) (fun x => rfl)
  have transU : ∀ u₀ : n → k, L ∘ₗ comapH (Homeomorph.addRight ((0 : X₁), (fromRows 0 (Matrix.of fun _ => u₀) : X₂))) = L := by
    intro u₀
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨⟨f, g⟩, rfl⟩
    have hc : IsLocallyConstant fun x : X₁ => (ψ (-(u₀ ⬝ᵥ fun r => x r (Sum.inr ()))) : ℂ) :=
      hψlc.comp_continuous (Continuous.neg (Continuous.dotProduct continuous_const
        (continuous_pi fun r => (continuous_apply (Sum.inr ())).comp (continuous_apply r))))
    set R : X₂ := fromRows 0 (Matrix.of fun _ => u₀)
    let f' := mulLC _ hc f
    let g' := comapH (Homeomorph.addRight R) g
    have hu : ∀ z : X₁ × X₂, uy (z + (0, R)) = uy z + u₀ ⬝ᵥ fun r => z.1 r (Sum.inr ()) := by
      intro z
      simp only [uy, Prod.fst_add, Prod.snd_add, add_zero, Matrix.add_apply, R, fromRows_apply_inr, Matrix.of_apply]
      rw [← add_dotProduct]; rfl
    have e1 : comapH (Homeomorph.addRight ((0 : X₁), R)) (mulLC _ hχ (prodSB f g)) = mulLC _ hχ (prodSB f' g') := by
      ext z
      simp only [comapH_apply, mulLC_apply, prodSB_apply, Homeomorph.coe_addRight, f', g']
      rw [hu, neg_add, coe_psi_add]
      simp only [Prod.fst_add, Prod.snd_add, add_zero]
      ring
    rw [LinearMap.comp_apply, e1, key, key]
    exact h1 u₀ f f' g g' (fun x => rfl) (fun x => rfl)

  set X₀ := Matrix n n' k × Matrix n'' n k
  have hc1 : Continuous fun z : X₁ × X₂ => ((z.1.toCols₁, z.2.toRows₁), ((fun r => z.2 (Sum.inr ()) r), (fun r => z.1 r (Sum.inr ())))) := by
    refine Continuous.prodMk (Continuous.prodMk ?_ ?_) (Continuous.prodMk ?_ ?_)
    · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
    · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply (Sum.inl i)).comp continuous_snd)
    · exact continuous_pi fun r => (continuous_apply r).comp ((continuous_apply (Sum.inr ())).comp continuous_snd)
    · exact continuous_pi fun r => (continuous_apply (Sum.inr ())).comp ((continuous_apply r).comp continuous_fst)
  have hc2 : Continuous fun w : X₀ × ((n → k) × (n → k)) =>
      ((fromCols w.1.1 (Matrix.of fun r _ => w.2.2 r) : X₁), (fromRows w.1.2 (Matrix.of fun _ => w.2.1) : X₂)) := by
    refine Continuous.prodMk ?_ ?_
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      rcases j with j | j
      · exact (continuous_apply j).comp ((continuous_apply i).comp (continuous_fst.comp continuous_fst))
      · exact (continuous_apply i).comp (continuous_snd.comp continuous_snd)
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      rcases i with i | i
      · exact (continuous_apply j).comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
      · exact (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  let e : X₁ × X₂ ≃ₜ X₀ × ((n → k) × (n → k)) :=
    { toFun := fun z => ((z.1.toCols₁, z.2.toRows₁), ((fun r => z.2 (Sum.inr ()) r), (fun r => z.1 r (Sum.inr ()))))
      invFun := fun w => (fromCols w.1.1 (Matrix.of fun r _ => w.2.2 r), fromRows w.1.2 (Matrix.of fun _ => w.2.1))
      left_inv := by
        rintro ⟨x₁, x₂⟩
        refine Prod.ext ?_ ?_
        · ext i j; rcases j with j | j <;> rfl
        · ext i j; rcases i with i | i <;> rfl
      right_inv := by
        rintro ⟨⟨p₁, p₂⟩, ⟨u, y⟩⟩
        rfl
      continuous_toFun := hc1
      continuous_invFun := hc2 }

  let L' : SB (X₀ × ((n → k) × (n → k))) →ₗ[ℂ] M := L ∘ₗ comapH e
  have hL' : ∀ (a : (n → k) × (n → k)) (G G' : SB (X₀ × ((n → k) × (n → k)))),
      (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L' G' = L' G := by
    rintro ⟨u₀, y₀⟩ G G' hG
    have h3 : comapH e G' = comapH (Homeomorph.addRight ((fromCols 0 (Matrix.of fun r _ => y₀ r) : X₁), (0 : X₂)))
        (comapH (Homeomorph.addRight ((0 : X₁), (fromRows 0 (Matrix.of fun _ => u₀) : X₂))) (comapH e G)) := by
      ext z
      simp only [comapH_apply, Homeomorph.coe_addRight]
      rw [hG]
      refine congrArg G.1 ?_
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      · ext i j; show z.1 i (Sum.inl j) = z.1 i (Sum.inl j) + 0 + 0; simp
      · ext i j; show z.2 (Sum.inl i) j = z.2 (Sum.inl i) j + 0 + 0; simp
      · ext r; show z.2 (Sum.inr ()) r + u₀ r = z.2 (Sum.inr ()) r + 0 + u₀ r; simp
      · ext r; show z.1 r (Sum.inr ()) + y₀ r = z.1 r (Sum.inr ()) + y₀ r + 0; simp
    rw [LinearMap.comp_apply, h3, ← LinearMap.comp_apply (f := L), transY, ← LinearMap.comp_apply (f := L), transU]
    rfl
  obtain ⟨l₀, hl₀⟩ := GlobalTheory.T.translationInvariant_schwartzBruhat_map_factors_integral k ν hν X₀ n n M L' hL'
  refine ⟨l₀, fun Ψ₁ Ψ₂ => ?_⟩
  obtain ⟨Ψ, hΨ, hLΨ⟩ := hl₀ (comapH e.symm (mulLC _ hχ (prodSB Ψ₁ Ψ₂)))
  refine ⟨Ψ, ?_, ?_⟩
  · funext p
    rw [hΨ]
    unfold contr hat
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [comapH_apply, mulLC_apply, prodSB_apply]
    have h4 : uy (e.symm (p, (u, y))) = u ⬝ᵥ y := rfl
    rw [h4, neg_one_mul]
    change (ψ (-(u ⬝ᵥ y)) : ℂ) * (Ψ₁.1 (fromCols p.1 (Matrix.of fun r _ => y r)) * Ψ₂.1 (fromRows p.2 (Matrix.of fun _ => u))) = _
    ring
  · rw [← key, ← hLΨ]
    show L _ = L _
    congr 1
    ext z
    simp only [comapH_apply, Homeomorph.symm_apply_apply]

end GlobalTheory.LocFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorBoxEqCharSum
section
open ValuativeRel Matrix GlobalTheory.SplitWeil
open scoped Topology

noncomputable section
namespace GlobalTheory.BoxCharComb

open GlobalTheory.LocMod.Inhab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_box_superset {K : Set (Matrix Y Y' k)} (hK : IsCompact K) :
    ∃ R : kˣ, ∀ x ∈ K, x ∈ box Y Y' R := by
  have h := hK.eventually_forall_of_forall_eventually (x₀ := (0 : k))
    (P := fun c x => c • x ∈ (box Y Y' (1 : kˣ) : Set (Matrix Y Y' k))) fun x _ =>
      (continuous_smul.tendsto' ((0 : k), x) 0 (zero_smul _ _)).eventually
        ((isOpen_box (Y := Y) (Y' := Y') (1 : kˣ)).mem_nhds (box Y Y' 1).zero_mem)
  obtain ⟨s, hs⟩ := exists_cball_subset h
  refine ⟨s⁻¹, fun x hx r q => ?_⟩
  have h1 : valuation k (((s : k) • x) r q) ≤ valuation k ((1 : kˣ) : k) :=
    hs (show (s : k) ∈ cball s from le_refl (valuation k (s : k))) x hx r q
  have e : x r q = (s : k)⁻¹ * (((s : k) • x) r q) := by
    rw [Matrix.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ s.ne_zero]
  rw [e, map_mul, Units.val_inv_eq_inv_val]
  exact mul_le_of_le_one_right' (by simpa only [Units.val_one, map_one] using h1)

end GlobalTheory.BoxCharComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearMapKillingPartialEvalIntegralKernelTransla
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.FlatFactor

theorem fill_add_single {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) (x : {e : m × m' // e ∈ it} → k) (e : m × m') (he : e ∈ it) (a : k) :
    fill ev it β t x + Matrix.single e.1 e.2 a = fill ev it β t (x + Pi.single ⟨e, he⟩ a) := by
  ext r q
  simp only [fill, Matrix.add_apply, Matrix.of_apply, Matrix.single_apply, Pi.add_apply]
  by_cases h : (r, q) ∈ it
  · rw [dif_pos h, dif_pos h]
    by_cases hrq : (r, q) = e
    · subst hrq
      simp [Pi.single_apply]
    · have h1 : ¬ (e.1 = r ∧ e.2 = q) := fun ⟨h1, h2⟩ => hrq (by rw [← h1, ← h2])
      have h2 : (⟨(r, q), h⟩ : {e : m × m' // e ∈ it}) ≠ ⟨e, he⟩ := fun h' => hrq (congrArg Subtype.val h')
      simp [h1, Pi.single_apply, h2]
  · rw [dif_neg h, dif_neg h]
    have h1 : ¬ (e.1 = r ∧ e.2 = q) := fun ⟨h1, h2⟩ => h (by rw [← h1, ← h2]; exact he)
    simp [h1]

theorem continuous_fill {k : Type} [Field k] [TopologicalSpace k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) : Continuous (fill ev it β t) := by
  refine continuous_pi fun r => continuous_pi fun q => ?_
  simp only [fill, Matrix.of_apply]
  by_cases h : (r, q) ∈ it
  · simp only [dif_pos h]; exact continuous_apply _
  · simp only [dif_neg h]; exact continuous_const

theorem hasCompactSupport_comp_fill {k : Type} [Field k] [TopologicalSpace k] [T2Space k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) (Θ : Matrix m m' k → ℂ) (hΘ : HasCompactSupport Θ) :
    HasCompactSupport (fun x => Θ (fill ev it β t x)) := by
  let pr : Matrix m m' k → ({e : m × m' // e ∈ it} → k) := fun T i => T i.1.1 i.1.2
  have hpr : Continuous pr := continuous_pi fun i => (continuous_apply i.1.2).comp (continuous_apply i.1.1)
  have hK : IsCompact (pr '' tsupport Θ) := hΘ.isCompact.image hpr
  refine HasCompactSupport.intro' hK hK.isClosed fun x hx => ?_
  by_contra h
  apply hx
  refine ⟨fill ev it β t x, subset_tsupport _ h, ?_⟩
  funext i
  simp [pr, fill, i.2]

theorem kerRed_translate_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ it, ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) := by
  intro k _ _ _ _ _ _ ψ ν _ _ hν m m' _ _ _ _ M _ _ l β ev it _ hK e he a Θ Θ' hΘ'
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  rw [← sub_eq_zero, ← map_sub]
  apply hK
  intro t
  have hint : Integrable (fun x => Θ.1 (fill ev it β t x)) (Measure.pi fun _ : {e : m × m' // e ∈ it} => ν) :=
    ((Θ.2.1.continuous).comp (continuous_fill ev it β t)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_fill ev it β t Θ.1 Θ.2.2)
  have hint' : Integrable (fun x => Θ.1 (fill ev it β t (x + Pi.single ⟨e, he⟩ a)))
      (Measure.pi fun _ : {e : m × m' // e ∈ it} => ν) :=
    hint.comp_add_right _
  unfold red
  simp only [Submodule.coe_sub, Pi.sub_apply]
  have h1 : ∀ x, Θ'.1 (fill ev it β t x) = Θ.1 (fill ev it β t (x + Pi.single ⟨e, he⟩ a)) := by
    intro x; rw [hΘ', fill_add_single]
  simp_rw [h1]
  rw [integral_sub hint' hint, integral_add_right_eq_self (fun x => Θ.1 (fill ev it β t x)), sub_self]

end GlobalTheory.FlatFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneIndexOfOneClassOfSupportOneStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symData_oneIndex_of_oneClass_of_supportOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneClass t ν → S.SupportOne t → S.OneIndex t ν := by
  first | exact @GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne | exact GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne | (intros; apply GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne <;> assumption)
end

