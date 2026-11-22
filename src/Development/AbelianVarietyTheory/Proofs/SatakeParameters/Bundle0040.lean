import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0523

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicRepEqOfEqAtAlmostAllSplitPlaces
section
namespace GlobalTheory.RowTie.RepDet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem isoLoc_perm {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa') (w : PlE H) : isoLoc N A Pa w = isoLoc N A Pa' w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l =>
    simp only [List.foldr_cons]
    rw [← A.lpSum_assoc, ← A.lpSum_assoc, A.lpSum_comm (spehLoc N A y w)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end GlobalTheory.RowTie.RepDet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem GlobalTheory.RowTie.repDet_split : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i →
    ∀ P P' : A.AV i, (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locV i P w = A.locV i P' w) → P = P' := by
  intro R H what₂ N A i hBC hSp hRep P P' hP
  obtain ⟨Pa, hPa⟩ := hBC P
  obtain ⟨Pa', hPa'⟩ := hBC P'
  have hperm := hSp P P' hP Pa Pa' hPa hPa'
  have hiso := GlobalTheory.RowTie.RepDet.isoLoc_perm N A hperm
  apply hRep P P'
  · intro w hw
    rw [← hPa.2.2.2.1 w hw, ← hPa'.2.2.2.1 w hw, hiso w]
  · intro w hw
    rw [← (hPa.2.2.2.2.1 w hw).2, ← (hPa'.2.2.2.2.1 w hw).2, hiso w]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EsymmInvMulEsymmCard
section
noncomputable section

namespace GlobalTheory.SatakeInv

open Matrix

variable {K : Type} [Field K] {r : ℕ}

def tinv : GL (Fin r) K →* GL (Fin r) K where
  toFun g := ⟨((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ, (g : Matrix (Fin r) (Fin r) K)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := by ext i j; simp [Matrix.one_apply, eq_comm]
  map_mul' g h := by ext : 1; simp [_root_.mul_inv_rev, transpose_mul]

theorem tinv_val (g : GL (Fin r) K) :
    ((tinv g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ :=
  rfl

theorem tinv_inv_val (g : GL (Fin r) K) :
    (((tinv g)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K)ᵀ :=
  rfl

theorem tinv_tinv (g : GL (Fin r) K) : tinv (tinv g) = g := by
  ext : 1
  rw [tinv_val, tinv_inv_val, transpose_transpose]

def scalGL (c : Kˣ) : GL (Fin r) K :=
  Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom c

theorem scalGL_val (c : Kˣ) :
    ((scalGL c : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = Matrix.scalar (Fin r) (c : K) := rfl

theorem scalGL_comm (c : Kˣ) (g : GL (Fin r) K) : scalGL c * g = g * scalGL c := by
  ext : 1
  simp only [Units.val_mul, scalGL_val]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)

theorem tinv_scalGL (c : Kˣ) : tinv (scalGL c : GL (Fin r) K) = scalGL c⁻¹ := by
  ext : 1
  have h : (scalGL c : GL (Fin r) K)⁻¹ = scalGL c⁻¹ := (map_inv (Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom) c).symm
  rw [tinv_val, h, scalGL_val, Matrix.scalar_apply, Matrix.diagonal_transpose]

theorem tinv_scalGL' (c : Kˣ) : tinv (scalGL c : GL (Fin r) K) = (scalGL c)⁻¹ := by
  rw [tinv_scalGL]
  exact map_inv (Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom) c

theorem tinv_injective : Function.Injective (tinv : GL (Fin r) K → GL (Fin r) K) := fun a b h => by
  rw [← tinv_tinv a, h, tinv_tinv]

omit [Field K] in

theorem glMap_eq_glMap_iff {O : Type} [CommRing O] [Field K] [Algebra O K] (a b : GL (Fin r) K)
    (L : Submodule O (Fin r → K)) :
    GlobalTheory.LatHecke.glMap a L = GlobalTheory.LatHecke.glMap b L ↔ GlobalTheory.LatHecke.glMap (a⁻¹ * b) L = L := by
  constructor
  · intro h
    rw [GlobalTheory.LatHecke.glMap_mul, ← h, ← GlobalTheory.LatHecke.glMap_mul, inv_mul_cancel, GlobalTheory.LatHecke.glMap_one]
  · intro h
    conv_lhs => rw [← h, ← GlobalTheory.LatHecke.glMap_mul, mul_inv_cancel_left]

theorem esymm_inv_mul_esymm_card (β : Multiset ℂ) (hβ : ∀ b ∈ β, b ≠ 0) {k : ℕ} (hk : k ≤ β.card) :
    (β.map (·⁻¹)).esymm k * β.esymm β.card = β.esymm (β.card - k) := by
  obtain ⟨n, α, rfl⟩ : ∃ (n : ℕ) (α : Fin n → ℂ), β = Finset.univ.val.map α := by
    induction β using Quotient.inductionOn with
    | h l => exact ⟨l.length, l.get, by simp⟩
  have hα : ∀ i, α i ≠ 0 := fun i => hβ _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val i))
  have hn : (Finset.univ.val.map α).card = n := by simp
  rw [hn] at hk ⊢
  simp only [Multiset.map_map, Finset.esymm_map_val, Function.comp_def]
  have h1 : Finset.powersetCard n (Finset.univ : Finset (Fin n)) = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [h1, Finset.sum_singleton, Finset.sum_mul]
  refine Finset.sum_nbij' compl compl (fun t ht => ?_) (fun t ht => ?_) (by simp) (by simp) fun t _ => ?_
  · simp only [Finset.mem_powersetCard_univ] at ht ⊢
    simp [Finset.card_compl, ht]
  · simp only [Finset.mem_powersetCard_univ] at ht ⊢
    rw [Finset.card_compl, ht, Fintype.card_fin]; omega
  · rw [← Finset.prod_mul_prod_compl t, ← mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl (fun i _ => inv_mul_cancel₀ (hα i)), Finset.prod_const_one, one_mul]

end GlobalTheory.SatakeInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisAdmissibleIffRepPureAvatar
section
noncomputable section

namespace GlobalTheory.GaloisInputCompare

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations.At GlobalTheory.IndefiniteRowSideFullHecke.GaloisRepresentations

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem norm_le_one_of_isIntegral {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := K)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff] at h
  exact_mod_cast h

theorem exists_inducesW (i : N.Loc) (τ : H.E →+* Qbar (N.l i)) :
    ∃ w ∈ placesOver H.E (N.l i), InducesW N i τ w := by
  have hle : ∀ x : 𝓞 H.E, ‖τ (x : H.E)‖ ≤ 1 := fun x =>
    norm_le_one_of_isIntegral (map_isIntegral_int τ (RingOfIntegers.isIntegral_coe x))
  let I : Ideal (𝓞 H.E) :=
    { carrier := {x | ‖τ (x : H.E)‖ < 1}
      zero_mem' := by simp
      add_mem' := fun {x y} hx hy => by
        change ‖τ ((x + y : 𝓞 H.E) : H.E)‖ < 1
        rw [show ((x + y : 𝓞 H.E) : H.E) = x + y from rfl, map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      smul_mem' := fun c x hx => by
        change ‖τ ((c * x : 𝓞 H.E) : H.E)‖ < 1
        rw [show ((c * x : 𝓞 H.E) : H.E) = c * x from rfl, map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hx }
  have hI : ∀ x : 𝓞 H.E, x ∈ I ↔ ‖τ (x : H.E)‖ < 1 := fun x => Iff.rfl
  have hl : ((N.l i : ℕ) : 𝓞 H.E) ∈ I := by
    rw [hI, show (((N.l i : ℕ) : 𝓞 H.E) : H.E) = (N.l i : ℕ) by simp, map_natCast,
      ← map_natCast (algebraMap ℚ_[N.l i] (PadicAlgCl (N.l i))), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hP : I.IsPrime := by
    refine ⟨fun h => ?_, fun {x y} h => ?_⟩
    · have := (hI 1).1 (h ▸ Submodule.mem_top)
      simp at this
    · rw [hI, show ((x * y : 𝓞 H.E) : H.E) = x * y from rfl, map_mul, norm_mul] at h
      by_contra hn
      rw [not_or, hI, hI, not_lt, not_lt] at hn
      exact absurd h (not_lt.2 (one_le_mul_of_one_le_of_one_le hn.1 hn.2))
  refine ⟨⟨I, hP, fun h => ?_⟩, hl, fun x => (hI x).symm⟩
  rw [h, Ideal.mem_bot] at hl
  exact (N.lPrime i).out.ne_zero (by exact_mod_cast hl)

def ClauseRep (i : N.Loc) : Prop :=
  ∀ a, 1 ≤ a → ∀ π : A.CG a, A.csd π → A.ralg π →
      ∃ ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)),
        Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) ∧
        IsSSRep ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) →
          A.wdOf i ρ w = A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2) ∧ A.tempered (A.locG π w)) ∧
        (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧
          (∀ τ, InducesW N i τ w → A.jumpsW i ρ τ = A.jumpsInf i π τ) ∧
          A.wdOf i ρ w = A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2))

def ClausePure : Prop :=
  ∀ a (π : A.CG a), A.ralg π → ∃ w₀ : ℂ, ∀ τ : H.E →+* ℂ,
      A.infG π (τ.comp (H.conj : H.E ≃ₐ[ℚ] H.E).toRingEquiv.toRingHom) = (A.infG π τ).map (w₀ - ·)

def ClauseChar (i : N.Loc) : Prop :=
  ∀ (χ : A.CG 1) (s : ℝ), (∀ τ : H.E →+* ℂ, ∀ z ∈ A.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) →
      ∃ ρ : G H.E N.Om →* GL (Fin 1) (Qbar (N.l i)), ContQ N i ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i ρ w = A.lpTw (A.locG χ w) s) ∧
        ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧ A.wdOf i ρ w = A.lpTw (A.locG χ w) s ∧
          ∀ τ, InducesW N i τ w → (A.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) =
            (A.infG χ ((A.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ)))

def PureRegular : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → A.ralg π →
    ∃ u : ℤ, ∀ τ : H.E →+* ℂ, A.infG π ((starRingEnd ℂ).comp τ) = (A.infG π τ).map (fun z => (u : ℂ) - z)

def PureSingular : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → IsAlg N A π → ¬ A.ralg π →
    ∃ u : ℤ, ∀ τ : H.E →+* ℂ, A.infG π ((starRingEnd ℂ).comp τ) = (A.infG π τ).map (fun z => (u : ℂ) - z)

def SelfDualWeightZero : Prop :=
  ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → IsAlg N A π → A.csd π →
    ∀ τ : H.E →+* ℂ, A.infG π ((starRingEnd ℂ).comp τ) = (A.infG π τ).map (fun z => -z)

open Classical in

def padded : NAut N :=
  { A with
    CG := fun a => A.CG a × Option ((H.E →+* ℂ) → ℂ)
    csd := fun p => A.csd p.1
    ralg := fun {a} p => A.ralg p.1 ∧ (2 ≤ a → p.2 = none)
    locG := fun p => A.locG p.1
    locG_dim := fun p => A.locG_dim p.1
    locG_unr_ae := fun p => A.locG_unr_ae p.1
    tw := fun p χ => (A.tw p.1 χ.1, p.2.map fun g τ => g τ + (A.infG χ.1 τ).sum)
    locG_tw := fun p χ => A.locG_tw p.1 χ.1
    infG := fun {a} p τ => if 2 ≤ a then p.2.elim (A.infG p.1 τ) fun g => Multiset.replicate a (g τ) else A.infG p.1 τ
    infG_card := fun {a} p τ => by
      obtain ⟨π, _ | g⟩ := p <;> by_cases h : 2 ≤ a <;> simp [h, A.infG_card]
    ralg_def := fun {a} p => by
      obtain ⟨π, _ | g⟩ := p
      · simpa using A.ralg_def π
      · by_cases h : 2 ≤ a
        · simp only [h, if_true, Option.elim, forall_true_left, reduceCtorEq, and_false, false_iff]
          intro hh
          obtain ⟨τ⟩ : Nonempty (H.E →+* ℂ) := inferInstance
          have := Multiset.nodup_iff_count_le_one.1 (hh τ).1 (g τ)
          rw [Multiset.count_replicate_self] at this
          omega
        · simpa [h] using A.ralg_def π
    infG_tw := fun {a} p χ τ s hs => by
      have hs' : A.infG χ.1 τ = {s} := by simpa using hs
      obtain ⟨π, _ | g⟩ := p <;> by_cases h : 2 ≤ a <;> simp [h, hs', A.infG_tw _ _ _ _ hs']
    csd_tw := fun p χ => A.csd_tw p.1 χ.1
    csd_unr := fun p => A.csd_unr p.1
    muC := fun i => (A.muC i, none)
    etaT := (A.etaT, none)
    etaTinv := (A.etaTinv, none)
    jumpsInf := fun i _ p => A.jumpsInf i p.1
    jumpsInf_def := fun i a p τ hr => by
      obtain ⟨π, o⟩ := p
      by_cases h : 2 ≤ a
      · obtain rfl : o = none := hr.2 h
        simpa using A.jumpsInf_def i π τ hr.1
      · simpa [h] using A.jumpsInf_def i π τ hr.1 }

end GlobalTheory.GaloisInputCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.H0TateDualNoInvariants
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.TateDualCoef

open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts TensorProduct

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

def coordEquiv :
    TensorProduct (N.O i) (Module.Dual (N.O i) (Fin R.r → N.O i)) (Kf N i) ≃ₗ[N.O i] (Fin R.r → Kf N i) :=
  (TensorProduct.congr (Pi.basisFun (N.O i) (Fin R.r)).dualBasis.equivFun (LinearEquiv.refl _ _)) ≪≫ₗ
    TensorProduct.comm (N.O i) (Fin R.r → N.O i) (Kf N i) ≪≫ₗ
      TensorProduct.piScalarRight (N.O i) (N.O i) (Kf N i) (Fin R.r)

theorem coordEquiv_tmul (f : Module.Dual (N.O i) (Fin R.r → N.O i)) (c : Kf N i) :
    coordEquiv N i (f ⊗ₜ c) = fun a => f (Pi.single a 1) • c := by
  ext a
  simp [coordEquiv, TensorProduct.piScalarRight_apply]

theorem tate_dual_single_basis (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (f : Module.Dual (N.O i) (Fin R.r → N.O i)) (a : Fin R.r) :
    (Glob.T2 N i ρ g f) (Pi.single a 1) =
      ∑ b, ((Glob.epsO N i g : (N.O i)ˣ) : N.O i) * ((((N.chi i 1 g⁻¹)⁻¹ : (N.O i)ˣ) : N.O i) *
        ((ρ g⁻¹ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)) b a) * f (Pi.single b 1) := by
  have hv : ∀ v : Fin R.r → N.O i, f v = ∑ b, v b * f (Pi.single b 1) := fun v => by
    conv_lhs => rw [pi_eq_sum_univ v]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [Glob.T2, Glob.Wp, twistRep, glRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply,
    Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, MonoidHom.inv_apply]
  rw [map_smul, hv]
  simp only [smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Matrix.toLin'_apply, Pi.smul_apply, mul_assoc]

theorem coordEquiv_equivariant (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (x : TensorProduct (N.O i) (Module.Dual (N.O i) (Fin R.r → N.O i)) (Kf N i)) :
    coordEquiv N i (coefRep (Glob.T2 N i ρ) (Kf N i) g x) = (matT N i ρ g).mulVec (coordEquiv N i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul f c =>
    have e1 : coefRep (Glob.T2 N i ρ) (Kf N i) g (f ⊗ₜ c) = (Glob.T2 N i ρ g f) ⊗ₜ c := rfl
    rw [e1, coordEquiv_tmul, coordEquiv_tmul]
    funext a
    rw [tate_dual_single_basis]
    simp only [Matrix.mulVec, dotProduct, matT, matW, Matrix.smul_apply, Matrix.transpose_apply,
      Matrix.map_apply, smul_eq_mul]
    simp only [Algebra.smul_def, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [eps, Glob.epsO]
    ring

theorem H0_coefRep_T2_comp_subtype_eq_bot_of_noInv : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)), GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matT N i ρ) → H0 ((Formalism.MainNotions.N.coefRep (Formalism.MainNotions.N.Glob.T2 N i ρ) (Kf N i)).comp Dg.subtype) = ⊥ := by
  intro R H what₂ N i ρ Dg h
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hfix : ∀ g ∈ Dg, (matT N i ρ g).mulVec (coordEquiv N i x) = coordEquiv N i x := by
    intro g hg
    rw [← coordEquiv_equivariant]
    congr 1
    exact (Representation.mem_invariants _ x).1 hx ⟨g, hg⟩
  have h0 := h _ hfix
  exact (coordEquiv N i).injective (by rw [h0, map_zero])

end GlobalTheory.TateDualCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.H0WeightPartNoInvariants
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.Ggeo.WpKInv

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def toPi (i : N.Loc) :
    TensorProduct (N.O i) (Fin R.r → N.O i) (FractionRing (N.O i)) ≃ₗ[N.O i] (Fin R.r → Kf N i) :=
  (TensorProduct.comm (N.O i) _ _).trans
    (TensorProduct.piScalarRight (N.O i) (N.O i) (FractionRing (N.O i)) (Fin R.r))

theorem toPi_tmul (i : N.Loc) (v : Fin R.r → N.O i) (k : FractionRing (N.O i)) :
    toPi N i (v ⊗ₜ k) = fun j => algebraMap (N.O i) (Kf N i) (v j) * k := by
  funext j
  simp [toPi, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]

theorem Wp_apply (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (v : Fin R.r → N.O i) :
    Glob.Wp N i ρ g v = ((((N.chi i 1 g)⁻¹ : (N.O i)ˣ) : N.O i) •
      ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))).mulVec v := by
  rw [Matrix.smul_mulVec]
  rfl

theorem toPi_WpK (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (g : G H.E N.Om)
    (t : TensorProduct (N.O i) (Fin R.r → N.O i) (FractionRing (N.O i))) :
    toPi N i (Glob.WpK N i ρ g t) = (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW N i ρ g).mulVec (toPi N i t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul v k =>
    have h1 : Glob.WpK N i ρ g (v ⊗ₜ k) = (Glob.Wp N i ρ g v) ⊗ₜ k := by
      simp [Glob.WpK, coefRep, Representation.tprod_apply]
    rw [h1, toPi_tmul, toPi_tmul, Wp_apply]
    have h2 : (fun j => algebraMap (N.O i) (Kf N i) (v j) * k) =
        k • (algebraMap (N.O i) (Kf N i) ∘ v) := by
      funext j; simp [mul_comm]
    rw [h2, Matrix.mulVec_smul]
    funext j
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW, ← RingHom.map_mulVec]

theorem H0_weight_part_eq_bot :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc)
      (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)),
      GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW N i ρ) →
        H0 ((Formalism.MainNotions.N.Glob.WpK N i ρ).comp Dg.subtype) = ⊥ := by
  intro R H what₂ N i ρ Dg h
  rw [eq_bot_iff]
  intro t ht
  rw [Submodule.mem_bot]
  have ht' : ∀ g ∈ Dg, Glob.WpK N i ρ g t = t := fun g hg =>
    (Representation.mem_invariants _ t).1 ht ⟨g, hg⟩
  have h0 : toPi N i t = 0 := h _ fun g hg => by rw [← toPi_WpK, ht' g hg]
  exact (toPi N i).map_eq_zero_iff.1 h0

end GlobalTheory.Ggeo.WpKInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowClose

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem isoLoc_eq_twSum_zero (P : List (Part A.CG)) (h : ∀ p ∈ P, p.d = 1) (w : PlE H) :
    isoLoc N A P w =
      GlobalTheory.RowTie.twSum N A (P.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))) w := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    have hp : p.d = 1 := h p (by simp)
    have h1 : spehLoc N A p w = A.lpTw (A.locG p.π w) 0 := by
      simp [spehLoc, hp, A.lpSum_zero]
    change A.lpSum (spehLoc N A p w) (isoLoc N A P w) = A.lpSum (A.lpTw (A.locG p.π w) 0) _
    rw [h1, ih fun q hq => h q (by simp [hq])]
    rfl

theorem isobaricCuspidalMultiplicityOne_of_twisted : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.IsobaricRigid N A → GlobalTheory.RowCopy.IsobaricCuspidalStrongMultiplicityOne N A := by
  intro R H what₂ N A hR Pa Pa' h h' hw
  have key := hR (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ)))
    (Pa'.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ)))
    (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact (h p hp).1)
    (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact (h' p hp).1)
    (hw.mono fun w e => by
      rw [← isoLoc_eq_twSum_zero N A Pa (fun p hp => (h p hp).2),
        ← isoLoc_eq_twSum_zero N A Pa' (fun p hp => (h' p hp).2), e])
  have back : ∀ P : List (Part A.CG), (∀ p ∈ P, p.d = 1) →
      (P.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))).map
        (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG)) = P := by
    intro P hP
    rw [List.map_map]
    conv_rhs => rw [← List.map_id P]
    refine List.map_congr_left fun p hp => ?_
    have := hP p hp
    obtain ⟨a, π, d⟩ := p
    simp only at this
    subst this
    rfl
  have := key.map (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG))
  rwa [back Pa (fun p hp => (h p hp).2), back Pa' (fun p hp => (h' p hp).2)] at this

end GlobalTheory.RowClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowSizeOfUnitarySphericalComponent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowSizeClosing

theorem rowSize_of_unitarySphericalComponent :
    ∀ (D : D7), GlobalTheory.RowSatakeBound.UnitarySphericalComponent D.nd D.naut → GlobalTheory.RowCopy.RowSize D :=
  fun D h => GlobalTheory.RowSatakeBound.rowSize_of_component D.nd D.naut h

end GlobalTheory.RowSizeClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLiftOfPairLift
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem pairs_of_thetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) (σ : what₂.FT) (P : A.AV i) (h : thetaOf N A i σ P) : GlobalTheory.ThetaExh.Pairs N A i σ P := by
  obtain ⟨hne, hle⟩ := h
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hF
  exact ⟨f, hf, _, hle hF, fun h0 => hF0 (inner_self_eq_zero.1 h0)⟩

theorem splitLift_of_pairLift : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.ThetaExh.SplitLift N A i :=
  fun _ _ _ N A i h σ P hθ => h σ P (pairs_of_thetaLift N A i σ P hθ)

end GlobalTheory.RowTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEvalOriginEqFibreTraceStatement
section
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_eval_origin_eq_fibre_trace : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ ev : rA k x {0} →ₐ[k] k, RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) → ∀ (h : rB k K x {0}) (a : rA k x {0}), (a : F) = Algebra.trace F K (h : K) → ev a = Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) := by
  first | (exact @GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot) | (exact GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot) | (intros; apply GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot  <;> assumption)
end

