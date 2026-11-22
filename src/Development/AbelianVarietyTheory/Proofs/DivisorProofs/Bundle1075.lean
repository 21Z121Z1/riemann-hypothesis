import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupRootsOfUnityTypedLieRanks
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section Abstract

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d d' : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
  {U : Matrix (Fin d) κ C} {L : Matrix κ (Fin d) C}

theorem cut_diagonal (hLU : L * U = 1) {j : Fin d' → κ} (hj : Function.Injective j) (t : κ → C) :
    L.submatrix j id * (U * Matrix.diagonal t * L) * U.submatrix id j = Matrix.diagonal fun b => t (j b) := by
  have h : L * (U * Matrix.diagonal t * L) * U = Matrix.diagonal t := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hLU, Matrix.one_mul, Matrix.mul_assoc, hLU, Matrix.mul_one]
  have h2 : L.submatrix j id * (U * Matrix.diagonal t * L) * U.submatrix id j =
      (L * (U * Matrix.diagonal t * L) * U).submatrix j j := by
    ext a b; simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  rw [h2, h, Matrix.submatrix_diagonal _ _ hj]; rfl

theorem proj_eq {j : Fin d' → κ} (hj : Function.Injective j) (t : κ → C) (h1 : ∀ b, t (j b) = 1)
    (h0 : ∀ ℓ, (¬ ∃ b, j b = ℓ) → t ℓ = 0) :
    U.submatrix id j * L.submatrix j id = U * Matrix.diagonal t * L := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_of_injOn j hj.injOn (fun _ _ => by simp) (fun ℓ _ hℓ => ?_) fun b' _ => by rw [h1, mul_one]
  rw [h0 ℓ (by simpa using hℓ), mul_zero, zero_mul]

theorem diagonal_mulVec (hLU : L * U = 1) (t : κ → C) (ℓ : κ) :
    (U * Matrix.diagonal t * L).mulVec (fun e => U e ℓ) = t ℓ • fun e => U e ℓ := by
  have h : U * Matrix.diagonal t * L * U = U * Matrix.diagonal t := by rw [Matrix.mul_assoc, hLU, Matrix.mul_one]
  funext e
  have := congrFun (congrFun h e) ℓ
  rw [Matrix.mul_diagonal, Matrix.mul_apply] at this
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this

theorem coord_mulVec (hLU : L * U = 1) (j : Fin d' → κ) (ℓ : κ) (b : Fin d') :
    (L.submatrix j id).mulVec (fun e => U e ℓ) b = if j b = ℓ then 1 else 0 := by
  have := congrFun (congrFun hLU (j b)) ℓ
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

theorem intSpan_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (u : β → Fin d → C) :
    intSpan v (fun a => u (e a)) = intSpan v u := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun k => a (e.symm k), fun k => ha _, by rw [← e.sum_comp]; simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun k => a (e k), fun k => ha _, by rw [← e.sum_comp]⟩

theorem nonempty_muAction (G : LogFGL v d) (p h : ℕ) (ty : Fin d → ZMod h)
    (hz : ∀ z : C, z ^ (p ^ h - 1) = 1 → ∃ φ, IsIntHom G G φ (Matrix.diagonal fun b => z ^ p ^ (ty b).val)) :
    Nonempty (MuAction G p h ty) := by
  classical
  choose φ hφ using hz
  refine ⟨⟨fun z => if hz : z ^ (p ^ h - 1) = 1 then φ z hz else 0, fun z hz a => ?_, fun z a => ?_, fun z hz a => ?_⟩⟩
  · rw [dif_pos hz]; exact (hφ z hz).2.1 a
  · split_ifs with hz
    · exact (hφ z hz).1 a
    · simp
  · rw [dif_pos hz, (hφ z hz).2.2 a]
    simp [Matrix.diagonal_apply, ite_smul]

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ} [Fact p.Prime]

theorem exists_orbit (X : ValExt T p) (hp : UnramIn E p) (τ : E →+* ℂ) :
    ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h ∧ ∃ lab : ZMod h → (E →+* ℂ), IsOrbit io X τ lab ∧
      (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) ∧
      ∀ z : X.C, z ^ (p ^ h - 1) = 1 → ∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1 := by
  obtain ⟨-, h, h0, hc⟩ := GlobalTheory.T.primeBelowComplexEmbeddingLabel_isMaximal_card E H l c p T io X τ
  haveI := charP_residueField_of_irreducible X
  obtain ⟨hon, F, Fp, Fs, Fi, Fk⟩ := GlobalTheory.T.ringHom_ker_eq_iff_frobeniusTwist (𝓞 E) _ p (red io X τ) h h0 (by rw [← primeBelow_eq_ker]; exact hc)
  obtain ⟨hi, hs⟩ := GlobalTheory.T.embeddingReducedResidueField_bijective_unramified E H l c p T io X hp
  choose lab hlab using fun s => hs (F s)
  refine ⟨h, h0, hc, lab, ⟨hi ?_, fun s a => ?_, fun s s' e => Fi ?_, fun σ => ?_⟩, fun s a => ?_, fun z hz => ?_⟩
  · rw [hlab]; ext a; rw [Fp]; simp
  · rw [← red_eq_pow_iff, hlab, hlab, Fs]
  · rw [← hlab, ← hlab, e]
  · rw [primeBelow_eq_ker, primeBelow_eq_ker, Fk]
    exact exists_congr fun s => by rw [← hlab, hi.eq_iff]
  · rw [← red_eq_pow_iff, hlab, Fp]
  · have hq : p ^ h - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow h0.ne' (Fact.out : p.Prime).one_lt)
    obtain ⟨z', hz'⟩ := X.ints.exists_of_le_one
      ((isIntV_iff X z).1 (le_of_eq (v_eq_zero_of_pow_eq_one hq hz).symm))
    have h1 : z' ^ p ^ h = z' := X.ints.hom_inj (by
      rw [map_pow, hz', ← Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.lt_of_sub_ne_zero hq)), pow_succ, hz, one_mul])
    obtain ⟨a, ha⟩ := hon (residue X.O z') (by rw [← map_pow, h1])
    refine ⟨a, ?_⟩
    rw [← hz', ← algebraMap_embO, ← residue_eq_iff_v]
    exact ha

variable [StarRing (𝓞 E)] {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p)

theorem exists_hom_of_approx [DecidableEq (Lt1 Dw)] {L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C}
    (hL : ∀ a b, IsIntV (vX_vp X) (L a b)) (hUL : (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1)
    (t : (E →+* ℂ) → X.C) (ht : ∀ r : ℝ, ∃ a : 𝓞 E, ∀ σ, (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a - t σ)) :
    ∃ φ, IsIntHom (fgl Ch X) (fgl Ch X) φ
      ((Matrix.of fun e ℓ => lieVec Ch X ℓ e) * Matrix.diagonal (fun ℓ : Lt1 Dw => t ℓ.1) * L) := by
  refine GlobalTheory.T.isIntegralLogHom_diagonal_of_limit X.C (vX_vp X) _ (fgl Ch X) (Lt1 Dw) _ L (fun e ℓ => isIntV_jX X _) hL hUL _ fun r => ?_
  obtain ⟨a, ha⟩ := ht r
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integers_act_integralChart_eigenDirections E H Dw l Xo c p T io X y Ch a
  exact ⟨fun ℓ => embX io X ℓ.1 a, _, _, h1, h2, fun ℓ => ha ℓ.1⟩

theorem typedPartAt (hp : UnramIn E p) (τ : E →+* ℂ) : TypedPartAt Ch X τ := by
  classical
  obtain ⟨h, h0, hc, lab, horb, hpow, hroot⟩ := exists_orbit (io := io) X hp τ
  haveI : NeZero h := ⟨h0.ne'⟩
  obtain ⟨L, hL, hLU, hUL⟩ := GlobalTheory.T.label_directions_integral_basis_unramified_prime E H Dw l Xo c p T io X y Ch hp
  set U : Matrix (Fin (chD Ch.ch)) (Lt1 Dw) X.C := Matrix.of fun e ℓ => lieVec Ch X ℓ e with hU
  obtain ⟨-, -, hinj, hker⟩ := id horb

  let t : X.C → (E →+* ℂ) → X.C := fun z => Function.extend lab (fun s => z ^ p ^ s.val) 0
  have ht1 : ∀ z s, t z (lab s) = z ^ p ^ s.val := fun z s => hinj.extend_apply _ _ s
  have ht0 : ∀ z σ, (¬ ∃ s, lab s = σ) → t z σ = 0 := fun z σ hσ => Function.extend_apply' _ _ σ hσ
  have happ : ∀ z : X.C, z ^ (p ^ h - 1) = 1 → ∀ r : ℝ, ∃ a : 𝓞 E, ∀ σ,
      (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a - t z σ) := by
    intro z hz r
    obtain ⟨a, h1, h2⟩ := GlobalTheory.T.exists_integers_approximating_root_of_unity_twists E H l c p T io X τ h h0 lab hpow z hz (hroot z hz) r
    refine ⟨a, fun σ => ?_⟩
    by_cases hσ : ∃ s, lab s = σ
    · obtain ⟨s, rfl⟩ := hσ
      rw [ht1]; exact h1 s
    · rw [ht0 z σ hσ, sub_zero]; exact h2 σ fun e => hσ ((hker σ).1 e)

  let K := Σ s : ZMod h, Fin (Dw.mult (lab s))
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let j₀ : K → Lt1 Dw := fun k => ⟨lab k.1, k.2⟩
  have hj₀ : Function.Injective j₀ := by
    rintro ⟨s, k⟩ ⟨s', k'⟩ hk
    obtain rfl : s = s' := hinj (congrArg Sigma.fst hk)
    obtain rfl : k = k' := eq_of_heq (Sigma.mk.inj hk).2
    rfl
  let j : Fin (Fintype.card K) → Lt1 Dw := fun b => j₀ (e b)
  have hj : Function.Injective j := hj₀.comp e.injective
  have hjr : ∀ ℓ : Lt1 Dw, (∃ s, lab s = ℓ.1) → ∃ b, j b = ℓ := by
    rintro ⟨σ, k⟩ ⟨s, rfl⟩
    exact ⟨e.symm ⟨s, k⟩, congrArg j₀ (e.apply_symm_apply _)⟩
  have hIP : U.submatrix id j * L.submatrix j id = U * Matrix.diagonal (fun ℓ : Lt1 Dw => t 1 ℓ.1) * L :=
    proj_eq hj _ (fun b => by rw [show (j b).1 = lab (e b).1 from rfl, ht1, one_pow])
      fun ℓ hℓ => ht0 1 _ fun hs => hℓ (hjr ℓ hs)
  have hPI : L.submatrix j id * U.submatrix id j = 1 := by
    have := cut_diagonal hLU hj (fun _ => 1)
    rwa [Matrix.diagonal_one, Matrix.mul_one, hUL, Matrix.mul_one, Matrix.diagonal_one] at this
  have hco : (1 : Matrix _ _ X.C) - U.submatrix id j * L.submatrix j id =
      U * Matrix.diagonal (fun ℓ : Lt1 Dw => 1 - t 1 ℓ.1) * L := by
    rw [hIP, ← Matrix.diagonal_sub, Matrix.diagonal_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUL]
  obtain ⟨G', ⟨ι', hι⟩, ⟨π', hπ⟩⟩ := GlobalTheory.T.logarithmic_group_law_split_by_idempotent X.C (vX_vp X) _ _ (fgl Ch X) (U.submatrix id j) (L.submatrix j id)
    (fun a b => isIntV_jX X _) (fun a b => hL _ _) hPI
    (by rw [hIP]; exact exists_hom_of_approx Ch X hL hUL (t 1) (happ 1 (one_pow _)))
    (by
      rw [hco]
      refine exists_hom_of_approx Ch X hL hUL (fun σ => 1 - t 1 σ) fun r => ?_
      obtain ⟨a, ha⟩ := happ 1 (one_pow _) r
      refine ⟨1 - a, fun σ => ?_⟩
      rw [map_sub (embX io X σ), map_one, sub_sub_sub_cancel_left, AddValuation.map_sub_swap]
      exact ha σ)
  have hfix : ∀ ℓ : Lt1 Dw, (U.submatrix id j * L.submatrix j id).mulVec (lieVec Ch X ℓ) =
      t 1 ℓ.1 • lieVec Ch X ℓ := fun ℓ => by
    rw [hIP]; exact diagonal_mulVec hLU _ ℓ
  have hco' : ∀ (ℓ : Lt1 Dw) b, (L.submatrix j id).mulVec (lieVec Ch X ℓ) b = if j b = ℓ then 1 else 0 :=
    fun ℓ b => coord_mulVec hLU j ℓ b
  let q : ∀ s, {b : Fin (Fintype.card K) // (e b).1 = s} ≃ Fin (Dw.mult (lab s)) := fun s =>
    (e.subtypeEquiv (q := fun k : K => k.1 = s) fun _ => Iff.rfl).trans (Equiv.sigmaSubtype s)
  have hq : ∀ s b, j b.1 = ⟨lab s, q s b⟩ := by
    rintro s ⟨b, rfl⟩; rfl
  refine ⟨h, h0, hc, lab, horb, _, G', fun b => (e b).1, U.submatrix id j, L.submatrix j id,
    ⟨⟨ι', hι⟩, ⟨π', hπ⟩, hPI, fun ℓ => ⟨fun hℓ => ?_, fun hℓ => ?_⟩⟩, nonempty_muAction _ _ _ _ fun z hz => ?_,
    fun s => ?_, fun s => ?_, fun s f hf => ⟨⟨fun a b => ?_, ?_⟩, fun a b hb => ?_, fun k => le_antisymm ?_ ?_⟩⟩
  · obtain ⟨s, hs⟩ := (hker _).1 hℓ
    rw [hfix, ← hs, ht1, one_pow, one_smul]
  · rw [hfix, ht0 1 _ fun hs => hℓ ((hker _).2 hs), zero_smul]
  · obtain ⟨φ, hφ⟩ := exists_hom_of_approx Ch X hL hUL (t z) (happ z hz)
    have := isIntHom_comp hι (isIntHom_comp hφ hπ)
    rw [cut_diagonal hLU hj] at this
    exact ⟨_, by simpa only [show ∀ b, (j b).1 = lab (e b).1 from fun _ => rfl, ht1] using this⟩
  · rw [← intSpan_equiv (q s)]
    congr 1
    funext b
    rw [← hq]; rfl
  · rw [Fintype.card_congr (q s), Fintype.card_fin, Dw.rank, Nat.add_sub_cancel]
    unfold Datum.mult InPsi
    congr
  · beta_reduce; rw [frame, hco']; unfold IsIntV; split_ifs <;> simp
  · choose r hr using fun a : Fin (rk f) => hjr ⟨f.1, Fin.castLE (rk_le f) a⟩ ⟨s, hf.symm⟩
    refine ⟨r, ?_⟩
    have : (Matrix.of fun a b => (L.submatrix j id).mulVec (frame Ch X f a) (r b)) = 1 := by
      ext a b
      rw [Matrix.of_apply, frame, hco', hr, Matrix.one_apply]
      simp [eq_comm]
    rw [this]; simp
  · rw [frame, hco', if_neg]
    intro hb'
    exact hb (hinj ((congrArg Sigma.fst hb').trans hf))
  · exact GlobalTheory.T.formalGroupDetPowDepth_le_of_integralLogHom X.C _ _ _ _ k _ _ _ _ hπ _
  · have := GlobalTheory.T.formalGroupDetPowDepth_le_of_integralLogHom X.C _ _ _ _ k _ _ _ _ hι fun a => (L.submatrix j id).mulVec (frame Ch X f a)
    simp only [Matrix.mulVec_mulVec, frame, hfix, hf, ht1, one_pow, one_smul] at this
    exact this

theorem formalGroupTypes : FormalGroupTypes := fun E _ _ _ H _ l _ c _ _ p _ hp T io X =>
  ⟨GlobalTheory.T.frobenius_acts_on_type_at_valuation E H l c p T io X, fun _ Ch τ => typedPartAt Ch X hp τ⟩

end GlobalTheory.PrimePart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralHermitianQuadraticCharacter
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussMain

section Scalar

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
  (c : E →ₐ[F] E) {δ : E} (hE : IsQuad c δ)

def sgnHom : Fˣ →* ℂ where
  toFun := sgn E
  map_one' := by simp only [sgn]; exact if_pos (one_mem _)
  map_mul' s t := GlobalTheory.T.localNormResidueSign_mul F E c δ hE s t

theorem sgn_inv (t : Fˣ) : sgn E t⁻¹ = sgn E t := by
  have h := (Units.map (Algebra.norm F : E →* F)).range.inv_mem_iff (x := t)
  unfold sgn
  by_cases ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · rw [if_pos ht, if_pos (h.mpr ht)]
  · rw [if_neg ht, if_neg (mt h.mp ht)]

variable {ν : Type} [Fintype ν] [DecidableEq ν]

theorem det_herm (a : GL ν E) (D : ν → Fˣ) :
    ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det =
      (Matrix.GeneralLinearGroup.det a : E) * c (Matrix.GeneralLinearGroup.det a : E) *
        algebraMap F E ((∏ j, D j : Fˣ) : F) := by
  have hm : ((a : Matrix ν ν E).map c).det = c (a : Matrix ν ν E).det := (RingHom.map_det (c : E →+* E) _).symm
  rw [det_mul, det_mul, det_transpose, det_diagonal, hm]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod, map_prod]
  ring

include hE in

theorem sc_det_inv (χ : Eˣ →* Circle) (m : ℕ) (hχ : ResEtaPow (R := F) ⊥ χ m) (a : GL ν E) (D : ν → Fˣ) :
    sc F χ m ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      (((distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det a)) : ℝ)⁻¹ ^ m : ℝ) : ℂ) *
        (∏ j, (sgn E (D j) * ((nabs F (D j))⁻¹ : ℝ))) ^ m := by
  obtain ⟨-, hmul, -, -, -, halg, hzc⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE m χ hχ
  set d : Eˣ := Matrix.GeneralLinearGroup.det a with hd
  have hdet : ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      ((d⁻¹ : Eˣ) : E) * c ((d⁻¹ : Eˣ) : E) * algebraMap F E (((∏ j, D j)⁻¹ : Fˣ) : F) := by
    rw [det_herm c a D]
    simp only [hd, Units.val_inv_eq_inv_val, map_inv₀, mul_inv]
  have e1 : nabs F (Units.map (Algebra.norm F : E →* F) d⁻¹) =
      ((distribHaarChar F (Units.map (Algebra.norm F : E →* F) d)) : ℝ)⁻¹ := by
    simp [nabs, map_inv]
  have e2 : sgn E (∏ j, D j)⁻¹ = ∏ j, sgn E (D j) := by
    rw [sgn_inv]; exact map_prod (sgnHom c hE) D Finset.univ
  have e3 : nabs F (∏ j, D j)⁻¹ = ∏ j, (nabs F (D j))⁻¹ := by
    simp [nabs, map_prod, map_inv]
  rw [hdet, hmul, hzc, halg, e1, e2, e3, Finset.prod_mul_distrib]
  push_cast
  ring

end Scalar

section Equiv

variable {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def glT (u : GL α E) : GL α E :=
  ⟨(u : Matrix α α E)ᵀ, ((u⁻¹ : GL α E) : Matrix α α E)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one], by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

def sandwich (U : GL α E) (A : GL ν E) : Matrix α ν E ≃ₜ+ Matrix α ν E where
  toFun x := (U : Matrix α α E) * x * (A : Matrix ν ν E)
  invFun y := ((U⁻¹ : GL α E) : Matrix α α E) * y * ((A⁻¹ : GL ν E) : Matrix ν ν E)
  left_inv x := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv y := by
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  map_add' x y := by simp only [Matrix.mul_add, Matrix.add_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end Equiv

theorem hasGauss_herm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ γ₀ : ℂ, ∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψ0 χ hχc hχ _ _ μ _
  haveI : IsTopologicalRing E := (GlobalTheory.T.quadExt_topological_properties F E c δ hE).2.1
  obtain ⟨u, D', hQd⟩ := GlobalTheory.T.exists_GL_diagonal_congruent_hermitian F E c δ hE α Q (Matrix.ext fun i j => hQ.1 i j) hQ.2.ne_zero
  obtain ⟨g0, hg0⟩ := GlobalTheory.T.gaussIntegral_diagonal_hermitianForm_matrices F E c δ hE α ν ψ hψ hψ1 hψ0 μ
  let s : α → Fˣ := fun i =>
    Units.mk0 (2⁻¹ * (D' i : F)) (mul_ne_zero (inv_ne_zero two_ne_zero) (D' i).ne_zero)
  let U : GL α E := glT u
  refine ⟨g0 * (((distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det U)) : ℝ)⁻¹ ^
    Fintype.card ν : ℝ) : ℂ) * (∏ i, (sgn E (s i) * ((nabs F (s i))⁻¹ : ℝ))) ^ Fintype.card ν, ?_⟩
  intro b hb hdet
  obtain ⟨a, D, rfl⟩ := GlobalTheory.T.exists_GL_diagonal_congruent_hermitian F E c δ hE ν b hb hdet
  let t : α → ν → Fˣ := fun i j => s i * D j
  have hfun : (fun x : Matrix α ν E => ψ (2⁻¹ * pr c Q x (x * ((a : Matrix ν ν E) *
      diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ)))) =
      fun x => (fun y : Matrix α ν E => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (y i j))) (sandwich U a x) := by
    funext x
    rw [GlobalTheory.T.hermitianMatrixColumnPairing_diagonal_norm F E c δ hE α ν Q hQ (u : Matrix α α E) (fun i => (D' i : F)) (a : Matrix ν ν E)
      (fun j => (D j : F)) hQd x]
    congr 1
  have key := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale (Matrix α ν E) (Matrix α ν E) μ μ (sandwich U a) _ _ _
    (GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt F E c δ hE α ν μ U a) (hg0 t)
  rw [hfun]
  convert key using 1
  rw [sc_det_inv c hE χ _ hχ a D]
  have ht : ∀ i j, sgn E (t i j) * (((nabs F (t i j))⁻¹ : ℝ) : ℂ) =
      (sgn E (s i) * (((nabs F (s i))⁻¹ : ℝ) : ℂ)) * (sgn E (D j) * (((nabs F (D j))⁻¹ : ℝ) : ℂ)) := by
    intro i j
    simp only [t]
    rw [GlobalTheory.T.localNormResidueSign_mul F E c δ hE, GlobalTheory.SplitWeil.nabs_mul F, mul_inv]
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ht i j]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
  push_cast
  ring

end GlobalTheory.KSp.GaussMain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEigenvalueAtBaseFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.HeckeUnitary

theorem isDC_central {G : Type} [Group G] (J : Subgroup G) {z : G} (hz : ∀ g, Commute z g) :
    Bridge.IsDC J z {z} := by
  refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
  rintro g ⟨k₁, k₂, rfl⟩
  refine ⟨z, ⟨Finset.mem_singleton_self z, ?_⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩
  rw [← (hz k₁).eq, mul_assoc, inv_mul_cancel_left]
  exact J.mul_mem k₁.2 k₂.2

theorem isDC_mul_central {G : Type} [Group G] [DecidableEq G] (J : Subgroup G) {z α : G} (hz : ∀ g, Commute z g)
    {R : Finset G} (h : Bridge.IsDC J α R) : Bridge.IsDC J (α * z) (R.image (· * z)) := by
  have e : ∀ k₁ k₂ : G, k₁ * (α * z) * k₂ = k₁ * α * k₂ * z := fun k₁ k₂ => by
    simp only [mul_assoc, (hz k₂).eq]
  have e' : ∀ a g : G, (a * z)⁻¹ * (g * z) = a⁻¹ * g := fun a g => by
    rw [mul_inv_rev, mul_assoc, ← mul_assoc a⁻¹, ← (hz (a⁻¹ * g)).eq, inv_mul_cancel_left]
  constructor
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
    exact ⟨k₁, k₂, (e _ _).symm⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := h.2 _ ⟨k₁, k₂, rfl⟩
    rw [e]
    refine ⟨a * z, ⟨Finset.mem_image_of_mem _ ha, by rwa [e']⟩, ?_⟩
    rintro y ⟨hy, hy'⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    rw [e'] at hy'
    rw [hu b ⟨hb, hy'⟩]

theorem star_eigenvalue_mul : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (PP : Pl D.host.E) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (c : ℕ → ℂ) (T : MMap M), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ P', P' ∈ L.Pg ∨ P' ∈ L.Q → P' ≠ PP ∧ ¬ IsConjPl P' PP) → Bridge.SplitOff PP ∅ → T ∈ Mult θ M (levG V β L : Set (GA D V)) (fun _ => 1) → ipM M μ 𝓕 T T ≠ 0 → (∀ k ≤ V.rank, ∀ α R, IsHeckeAt V PP k α → Bridge.IsDC (levG V β L) α⁻¹ R → heckeOn M R T = c k • T) → c V.rank ≠ 0 ∧ ∀ k ≤ V.rank, star (c k) * c V.rank = c (V.rank - k) := by
  intro D V S θ M β Λ N L PP μ 𝓕 c T hμ h𝓕 hβ hN hL hsp hT hip hc
  classical
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : SecondCountableTopology (GA D V) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have : Countable (GQ V) := (GlobalTheory.RationalCountable.discrete_countable_GQ D V).2
  have : μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT
  have hex : ∃ a, IsMultIP M μ 𝓕 T T a := by
    by_contra hne
    exact hip (by unfold ipM; rw [dif_neg hne])
  have hIP := ipM_spec M μ 𝓕 T T hex
  choose v hv hv0 using fun τ => (Submodule.ne_bot_iff _).1 (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  let w : M.Vec := fun τ => ⟨v τ, hv τ⟩
  obtain ⟨hint, hval⟩ := hIP w w
  have hne : ∫ g in 𝓕, star (T w g) * T w g ∂μ ≠ 0 := by
    rw [hval]
    exact mul_ne_zero hip (Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 (hv0 τ))
  obtain ⟨g₀, hg₀⟩ : ∃ g, T w g ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hne (by simp [h0])
  have hc' : ∀ k ≤ V.rank, ∀ α R, IsHeckeAt V PP k α → Bridge.IsDC (levG V β L) α⁻¹ R →
      ∀ g, ∑ γ ∈ R, T w (g * γ) = c k * T w g := fun k hk α R h1 h2 g =>
    congrArg (fun T' : MMap M => T' w g) (hc k hk α R h1 h2)
  obtain ⟨z, hz, hzn, hk⟩ := GlobalTheory.T.central_hecke_element_exists V β Λ N L PP hβ hN hL hsp
  have hz' : ∀ g, Commute z⁻¹ g := fun g => (hz g).inv_left
  have hcen : ∀ g, T w (g * z⁻¹) = c V.rank * T w g := fun g => by
    simpa using hc' V.rank le_rfl z {z⁻¹} hzn (isDC_central _ hz') g
  have hn : c V.rank ≠ 0 := fun h0 => hg₀ (by simpa [h0] using hcen (g₀ * z))
  refine ⟨hn, fun k hkn => ?_⟩
  obtain ⟨α, R, R', h1, h2, h3, h4, h5⟩ := hk k hkn
  have h6 : ∀ g, ∑ γ ∈ R', T w (g * γ) = c (V.rank - k) / c V.rank * T w g := fun g => by
    have := hc' (V.rank - k) (Nat.sub_le _ _) (z * α⁻¹) (R'.image (· * z⁻¹)) h2
      (by rw [mul_inv_rev, inv_inv]; exact isDC_mul_central _ hz' h4) g
    rw [Finset.sum_image (fun a _ b _ hab => mul_right_cancel hab)] at this
    simp only [← mul_assoc, hcen, ← Finset.mul_sum] at this
    rw [div_mul_eq_mul_div, ← this, mul_div_cancel_left₀ _ hn]
  have h7 := GlobalTheory.DoubleCosetAdjoint.eigenvalue_inv_eq_star μ (GQ V) (levG V β L) 𝓕 (T w) α⁻¹ R R' (c k)
    (c (V.rank - k) / c V.rank) h𝓕 (hT'.aut w).cont (hT'.aut w).left
    (fun k hk g => by simpa using hT'.lev w k hk g) hint hne h3 (by rwa [inv_inv]) h5
    (hc' k hkn α R h1 h3) h6
  rw [h7, div_mul_cancel₀ _ hn]

end GlobalTheory.HeckeUnitary

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

variable {p : ℕ} [Fact p.Prime]

def IntC (G : HTGroup p) (w : AwayP p) (a : w.1.adicCompletion ℚ ⊗[ℚ] G.C) : Prop :=
  ∀ i, coordL G w a i ∈ w.1.adicCompletionIntegers ℚ

end GlobalTheory.FinClsLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOrderCentralizerStable
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_order_centralizer_stable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (g : (Qv v ⊗[ℚ] G.C)ˣ) (c : (Qv v)ˣ), (g : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) g).unop = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c → IsIntV G v 1 → (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) → (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) → (∀ y z : Qv v ⊗[ℚ] G.C, y * g = g * y → z * g = g * z → y * z = z * y) → ∀ θ θ' h : Qv v ⊗[ℚ] G.C, θ * g = g * θ → θ' * g = g * θ' → h * g = g * h → IsIntV G v θ → IsIntV G v θ' → IsIntV G v h → (θ - (starT G.star (Qv v) θ).unop) * θ' = 1 → 2 * h = 1 → ∀ s : (Qv v ⊗[ℚ] G.C)ˣ, s * g = g * s → IsIntV G v (s : Qv v ⊗[ℚ] G.C) → IsIntV G v ((s⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) → (starT G.star (Qv v) s).unop = s → ∃ u : (Qv v ⊗[ℚ] G.C)ˣ, u * g = g * u ∧ IsIntV G v (u : Qv v ⊗[ℚ] G.C) ∧ IsIntV G v ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧ (u : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) u).unop = s := by
  first | (exact @GlobalTheory.OrbFinAf.normStep_exists) | (exact GlobalTheory.OrbFinAf.normStep_exists) | (intros; apply GlobalTheory.OrbFinAf.normStep_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactIntegralUnitaryPointsAtPlaceStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_integralUnitaryPointsAtPlace : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), IsCompact (IntV G v) := by
  first | (exact @GlobalTheory.OrbFinAf.isCompact_IntV) | (exact GlobalTheory.OrbFinAf.isCompact_IntV) | (intros; apply GlobalTheory.OrbFinAf.isCompact_IntV  <;> assumption)
end

