import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0615
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.HeckeP

theorem mem_range_map_subtype {B : Type} [CommRing B] (R : Subring B) {n : ℕ} (g : GL (Fin n) B) :
    g ∈ (GeneralLinearGroup.map R.subtype).range ↔
      (∀ i j, (g : Matrix (Fin n) (Fin n) B) i j ∈ R) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact ((h : Matrix (Fin n) (Fin n) R) i j).2
    · rw [← map_inv]; exact ((h⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j |>.2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => ⟨_, h1 i j⟩
    let M' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hinj : Function.Injective (fun X : Matrix (Fin n) (Fin n) R => X.map R.subtype) :=
      fun X Y e => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun e i) j)
    have hM : M.map R.subtype = (g : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
    have hM' : M'.map R.subtype = ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
    have e1 : M * M' = 1 := hinj (by
      show (M * M').map R.subtype = (1 : Matrix (Fin n) (Fin n) R).map R.subtype
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv)
    have e2 : M' * M = 1 := hinj (by
      show (M' * M).map R.subtype = (1 : Matrix (Fin n) (Fin n) R).map R.subtype
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul)
    exact ⟨⟨M, M', e1, e2⟩, Units.ext hM⟩

variable (p : ℕ) [Fact p.Prime]

theorem inclK_mem_intKQ_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (a : K) :
    inclK p K r a ∈ intKQ p K r ↔ a ∈ GlobalTheory.LKLoc.intK p K := by
  constructor
  · intro h
    have h1 := GlobalTheory.LKRes.Model.mulMap_intKQ p K r _ h
    have h2 : GlobalTheory.LKRes.Model.mulMap p K r (inclK p K r a) = (a : PadicAlgCl p) := by
      show (a : PadicAlgCl p) * 1 = _
      rw [mul_one]
    rw [h2] at h1
    exact (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff (p := p)).2 h1
  · intro h
    exact Subring.subset_closure (Or.inl ⟨⟨a, h⟩, rfl⟩)

theorem map_inclK_mem_Kres_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (g : GL (Fin n) K) :
    GeneralLinearGroup.map (inclK p K r).toRingHom g ∈ Kres p K n r ↔ g ∈ GlobalTheory.LKLoc.KintK p K n := by
  unfold Kres GlobalTheory.LKLoc.KintK
  rw [mem_range_map_subtype, mem_range_map_subtype, ← map_inv]
  simp only [GeneralLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map, RingHom.mapMatrix_apply]
  simp [Matrix.map_apply, inclK_mem_intKQ_iff]

theorem scalar_mem_Kint_iff (r : ℕ) (s : ℚ_[p]ˣ) :
    (GeneralLinearGroup.scalar (Fin 1)) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom s) ∈
        GlobalTheory.LKLoc.Kint p (Q0 p) 1 r ↔ ‖(s : ℚ_[p])‖ ≤ 1 ∧ ‖((s⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := by
  unfold GlobalTheory.LKLoc.Kint
  rw [mem_range_map_subtype, ← map_inv, ← map_inv]
  have key : ∀ t : ℚ_[p], algebraMap ℚ_[p] (Qr p r) t ∈ GlobalTheory.LKLoc.intR p (Q0 p) r ↔ ‖t‖ ≤ 1 := by
    intro t
    rw [GlobalTheory.LKLoc.intR, Subring.mem_comap, ValuationSubring.mem_toSubring, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff,
      ← IsScalarTower.algebraMap_apply, PadicAlgCl.norm_extends]
  have key' : ∀ t : ℚ_[p], (algebraMap ℚ_[p] (Qr p r) t)⁻¹ ∈ GlobalTheory.LKLoc.intR p (Q0 p) r ↔ ‖t‖⁻¹ ≤ 1 := by
    intro t; rw [← map_inv₀, key, norm_inv]
  simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, key, key']

theorem inclG_mem_KHT_iff (G : HTGroup p) (r : ℕ) (x : Gp G) :
    inclG G r x ∈ KHT p G.m G.n r G.Fw ↔
      (‖(x.1 : ℚ_[p])‖ ≤ 1 ∧ ‖((x.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) ∧
        ∀ w, x.2 w ∈ GlobalTheory.LKLoc.KintK p (G.Fw w) G.n := by
  unfold KHT
  rw [Subgroup.mem_prod, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies]
  have h1 : (inclG G r x).1 =
      (GeneralLinearGroup.scalar (Fin 1)) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom x.1) := rfl
  have h2 : ∀ w, (inclG G r x).2 w = GeneralLinearGroup.map (inclK p (G.Fw w) r).toRingHom (x.2 w) :=
    fun w => rfl
  rw [h1, scalar_mem_Kint_iff]
  simp only [h2, map_inclK_mem_Kres_iff]

theorem gl_one_map_conj {R : Type} [CommRing R] (H : Subgroup (GL (Fin 1) R)) (g : GL (Fin 1) R) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  have hc : ∀ a b : GL (Fin 1) R, a * b = b * a := fun a b => by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  have : (MulAut.conj g).toMonoidHom = MonoidHom.id _ := MonoidHom.ext fun x => by
    show g * x * g⁻¹ = x
    rw [hc g x, mul_inv_cancel_right]
  rw [this, Subgroup.map_id]

theorem Kres_commensurable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (n r : ℕ) (hr : 0 < r) (g : GL (Fin n) (KQ p K r)) :
    Subgroup.Commensurable ((Kres p K n r).map (MulAut.conj g).toMonoidHom) (Kres p K n r) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) :=
    ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
  have mono : ∀ (x : KQ p K r) (k l : ℕ), k ≤ l → (p : KQ p K r) ^ k * x ∈ intKQ p K r →
      (p : KQ p K r) ^ l * x ∈ intKQ p K r := by
    intro x k l hkl h
    rw [← Nat.add_sub_cancel' hkl, pow_add, mul_comm ((p : KQ p K r) ^ k), mul_assoc]
    exact mul_mem (pow_mem (natCast_mem _ p) _) h
  choose f hf using GlobalTheory.T.exists_padic_pow_mul_mem_tensorUnramifiedIntegers p K r
  let k : ℕ := (Finset.univ.sup fun ij : Fin n × Fin n => f ((g : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) ⊔
    Finset.univ.sup fun ij : Fin n × Fin n => f (((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)
  have hk1 : ∀ i j, (p : KQ p K r) ^ k * (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r :=
    fun i j => mono _ _ _ (le_sup_left.trans' (Finset.le_sup (f := fun ij : Fin n × Fin n =>
      f ((g : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) (Finset.mem_univ (i, j)))) (hf _)
  have hk2 : ∀ i j, (p : KQ p K r) ^ k *
      ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r :=
    fun i j => mono _ _ _ (le_sup_right.trans' (Finset.le_sup (f := fun ij : Fin n × Fin n =>
      f (((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) (Finset.mem_univ (i, j)))) (hf _)
  let c : intKQ p K r := (p : intKQ p K r) ^ k
  have hc : (c : KQ p K r) = (p : KQ p K r) ^ k := by simp [c]
  have hfin : Finite (intKQ p K r ⧸ Ideal.span {c * c}) := by
    have h := GlobalTheory.T.finite_padicTensorUnramifiedIntegers_quot_primePow p K r (2 * k) (GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim p K (2 * k)) (GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim p (Qr p r) (2 * k))
    have e : c * c = (p : intKQ p K r) ^ (2 * k) := by simp only [c]; ring
    rw [e]; exact h
  exact GlobalTheory.T.commensurable_conj_range_gl_map_subtype (intKQ p K r) n c hfin g (fun i j => by rw [hc]; exact hk1 i j)
    (fun i j => by rw [hc]; exact hk2 i j)

end GlobalTheory.HeckeP

open GlobalTheory.HeckeP in

theorem GlobalTheory.heckeOperator_integral :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r →
      (∀ g : Gr G r, Subgroup.Commensurable ((KHT p G.m G.n r G.Fw).map (MulAut.conj g).toMonoidHom)
        (KHT p G.m G.n r G.Fw)) ∧
      (KHT p G.m G.n r G.Fw).comap (inclG G r) = Kp0 G ∧
      (KHT p G.m G.n r G.Fw).map (sigG G r) ≤ KHT p G.m G.n r G.Fw := by
  intro p _ G r hr
  refine ⟨fun g => ?_, ?_, ?_⟩
  · unfold KHT
    exact GlobalTheory.T.commensurable_map_conj_prod_pi' _ _ g (by rw [gl_one_map_conj])
      (fun i => Kres_commensurable p (G.Fw i) G.n r hr (g.2 i))
  · ext x
    rw [Subgroup.mem_comap, Kp0, Subgroup.mem_comap, inclG_mem_KHT_iff, inclG_mem_KHT_iff]
  · rintro _ ⟨x, hx, rfl⟩
    exact GlobalTheory.LKRes.Model.sigHT_KHT p _ _ _ _ x hx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ClsReg

theorem conj_rel_alg' {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β e e' : G.Cˣ) (a' : G.C) (r r' : ℚˣ) :
    algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) =
      algebraMap ℚ G.C ((r : ℚ) / r') * (((e * e'⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (r' : ℚ) *
        ((e' : G.C) * a' * ((β : G.C) * sh G (e' : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))) *
        ((β : G.C) * sh G ((e * e'⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  have hsh : sh G ((e * e'⁻¹ : G.Cˣ) : G.C) = sh G ((e'⁻¹ : G.Cˣ) : G.C) * sh G (e : G.C) := by
    simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
  have h1 : sh G (e' : G.C) * sh G ((e'⁻¹ : G.Cˣ) : G.C) = 1 := by
    simp only [sh]
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hrr : (r' : ℚ) * ((r : ℚ) / r') = r := by field_simp
  have key2 : ((e : G.C) * ((e'⁻¹ : G.Cˣ) : G.C)) * ((e' : G.C) * a' * ((β : G.C) * sh G (e' : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) *
      ((β : G.C) * (sh G ((e'⁻¹ : G.Cˣ) : G.C) * sh G (e : G.C)) * ((β⁻¹ : G.Cˣ) : G.C)) =
      (e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
    simp only [mul_assoc]
    rw [Units.inv_mul_cancel_left, Units.inv_mul_cancel_left, ← mul_assoc (sh G (e' : G.C)), h1, one_mul]
  rw [hsh, Units.val_mul]
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, hrr]
  rw [key2]

theorem commute_of_commute_of_separable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (y₀ : G.C)
    (hsep : (minpoly G.F y₀).Separable) (hdeg : (minpoly G.F y₀).natDegree = G.n) (a b : G.C)
    (ha : Commute a y₀) (hb : Commute b y₀) : Commute a b := by
  have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC y₀ hsep hdeg
  have hamem : a ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact ha.eq.symm
  have hbmem : b ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hb.eq.symm
  rw [hc] at hamem
  have h2 := Algebra.adjoin_le_centralizer_centralizer G.F ({y₀} : Set G.C) hamem
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact (h2 b hbmem).symm

theorem units_conj_of_minpoly_eq_of_separable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (a b : G.Cˣ)
    (hab : minpoly G.F (a : G.C) = minpoly G.F (b : G.C)) (hsep : (minpoly G.F (b : G.C)).Separable)
    (hdeg : (minpoly G.F (b : G.C)).natDegree = G.n) : ∃ g : G.Cˣ, (a : G.C) = g * b * ↑g⁻¹ := by
  haveI : Infinite G.F := Infinite.of_injective (Nat.cast : ℕ → G.F) Nat.cast_injective
  obtain ⟨g, hg⟩ := GlobalTheory.LKInv.exists_unit_conj_of_minpoly_eq G.F G.C G.n G.rankC (b : G.C) (a : G.C) hsep hdeg hab
  refine ⟨g, ?_⟩
  rw [hg, mul_assoc, Units.mul_inv, mul_one]

end GlobalTheory.LKCx.ClsReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
section
noncomputable section

namespace GlobalTheory.ChrWUnif

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance locField (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

theorem valued_unifAt (v : Pl F) : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  have hu : valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) = uniformizer (Fv F v) :=
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπv : Valued.v ((π : F) : Fv F v) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hlt : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) < 1 :=
    e.lt_one_iff_lt_one.1 (hu ▸ uniformizer_lt_one)
  have h0 : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) ≠ 0 := by simp
  have hle1 : valuation (Fv F v) ((π : F) : Fv F v) ≤ valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) := by
    rw [hu, le_uniformizer_iff]
    exact e.lt_one_iff_lt_one.2 (by rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) := hπv ▸ (e _ _).1 hle1
  rw [← WithZero.exp_log h0] at hlt hge ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hge
  congr 1
  omega

theorem chrW_unifAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E)
    (v : Pl F) (t : E →ₐ[F] Fv F v) (h : UnrAt χ (splitPrime t)) : chrW χ t (unifAt v) = val χ (splitPrime t) := by
  refine h.locChar_eq_val ?_
  show Valued.v (complMap (splitPrime_under t) ((unifAt v : (Fv F v)ˣ) : Fv F v)) = WithZero.exp (-1 : ℤ)
  rw [GlobalTheory.LFun.SplitTie.valued_complMap t (splitPrime_under t), valued_unifAt]

end GlobalTheory.ChrWUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtensionProductDecomposition
section
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes.ResSplit

theorem mem_intR_iff (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ)
    (x : Kn p K n) : x ∈ GlobalTheory.LKLoc.intR p K n ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  show (algebraMap (Kn p K n) (PadicAlgCl p) x) ∈ Obar p ↔ _
  exact mem_Obar_iff

theorem comp_mem_intR (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {f : ℕ}
    (hq : qK p K = p ^ f) (r i : ℕ) (x : KQ p K r) (hx : x ∈ intKQ p K r) :
    comp p K hq r i x ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r) := by
  have h : intKQ p K r ≤ (GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)).comap (comp p K hq r i).toRingHom := by
    apply Subring.closure_le.2
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · show comp p K hq r i (inclK p K r (a : K)) ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)
      rw [mem_intR_iff p K (r / Nat.gcd f r), comp_inclK]
      exact mem_Obar_iff.1 a.2
    · show comp p K hq r i (inclQ p K r (b : Qr p r)) ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)
      rw [mem_intR_iff p K (r / Nat.gcd f r), comp_inclQ, norm_GK]
      exact mem_Obar_iff.1 b.2
  exact h hx

theorem kq_split : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K →
    ∀ (f r : ℕ), qK p K = p ^ f → 0 < r →
    ∃ (e : KQ p K r ≃+* (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r)))
      (τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r)),
      (∀ x, (τ x = x ↔ (x : PadicAlgCl p) ∈ K)) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧
      (∀ (a : K) (i : Fin (Nat.gcd f r)), ((e (inclK p K r a) i : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = a) ∧
      (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)) (h : i.val + 1 < Nat.gcd f r),
        e (sigKQ p K r x) i = e x ⟨i.val + 1, h⟩) ∧
      (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)), i.val + 1 = Nat.gcd f r → ∀ (i0 : Fin (Nat.gcd f r)),
        i0.val = 0 → e (sigKQ p K r x) i = τ (e x i0)) ∧
      (∀ x : KQ p K r, x ∈ intKQ p K r ↔ ∀ i, e x i ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)) := by
  intro p _ K hK f r hq hr
  have hp := (Fact.out : p.Prime)
  have h1r : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp.pos
  have hN : ¬ p ∣ p ^ r - 1 := by
    intro h
    have h2 : p ∣ 1 := (Nat.dvd_add_right h).1 (by rw [Nat.sub_add_cancel h1r]; exact dvd_pow_self p hr.ne')
    exact hp.not_dvd_one h2
  have hN0 : p ^ r - 1 ≠ 0 := fun h => hN (h ▸ dvd_zero p)
  obtain ⟨ζ, hζ⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hN0
  have hζmem : ζ ∈ Qr p r := UnramifiedExtensions.mem_Kn_of_pow (Q0 p) (by rw [residue_cardinality_base_field]; exact hζ.pow_eq_one)
  set ζ' : Qr p r := ⟨ζ, hζmem⟩ with hζ'
  have hfr : ∀ i : ℕ, (frobK p (Q0 p) ^ i) ζ = ζ ^ p ^ i := fun i => frobenius_pow_root_of_unity p hN hζ.pow_eq_one i

  have val : ∀ (c : Fin r → K) (i : ℕ),
      ((comp p K hq r i (∑ j : Fin r, inclK p K r (c j) * inclQ p K r ζ' ^ (j : ℕ)) : Kn p K (r / Nat.gcd f r)) :
        PadicAlgCl p) = ∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ) := by
    intro c i
    rw [map_sum, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, comp_inclK, comp_inclQ]
    rw [show ((ζ' : Qr p r) : PadicAlgCl p) = ζ from rfl, hfr]

  have key : ∀ c : Fin r → K, (∀ i < Nat.gcd f r, ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)‖ ≤ 1) →
      ∀ j, ‖(c j : PadicAlgCl p)‖ ≤ 1 := by
    intro c hc j
    refine GlobalTheory.T.coefficients_bounded_roots_unity p (p ^ r - 1) r hN (fun s => ζ ^ p ^ (s : ℕ)) ?_ ?_ (fun j => (c j : PadicAlgCl p)) ?_ j
    · intro s
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · intro s t hst
      rcases Nat.lt_or_ge r 2 with hr2 | hr2
      · apply Fin.ext
        have := s.2; have := t.2
        omega
      · have hlt : ∀ u : Fin r, p ^ (u : ℕ) < p ^ r - 1 := by
          intro u
          have h1 : p ^ (u : ℕ) ≤ p ^ (r - 1) := Nat.pow_le_pow_right hp.pos (by omega)
          have h2 : p ^ r = p * p ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
          have h3 : 2 ≤ p ^ (r - 1) := le_trans hp.two_le (by
            calc p = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ (r - 1) := Nat.pow_le_pow_right hp.pos (by omega))
          have h4 : 2 * p ^ (r - 1) ≤ p * p ^ (r - 1) := Nat.mul_le_mul_right _ hp.two_le
          omega
        have h5 := hζ.pow_inj (hlt s) (hlt t) hst
        exact Fin.ext (Nat.pow_right_injective hp.two_le h5)
    · intro s
      obtain ⟨i, hi, heq⟩ := GlobalTheory.T.norm_sum_frobenius_gcd p K hK f r hq hr ζ hζ.pow_eq_one c s
      rw [heq]
      exact hc i hi

  have inj : Function.Injective (eMap p K hq r) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := GlobalTheory.T.unramified_extension_basis p K r hr ζ' hζ x
    have hz : ∀ i < Nat.gcd f r, ∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ) = 0 := by
      intro i hi
      rw [← val c i]
      have h1 := congrFun hx ⟨i, hi⟩
      rw [eMap_apply] at h1
      rw [h1]
      rfl
    have hc0 : ∀ j, c j = 0 := by
      intro j
      by_contra hcj
      have h1 := key (fun k => ((p : K)⁻¹ * (c j)⁻¹) * c k) (by
        intro i hi
        have h2 : ∑ k : Fin r, (((((p : K)⁻¹ * (c j)⁻¹) * c k : K)) : PadicAlgCl p) * (ζ ^ p ^ i) ^ (k : ℕ) =
            (((p : K)⁻¹ * (c j)⁻¹ : K) : PadicAlgCl p) *
              ∑ k : Fin r, (c k : PadicAlgCl p) * (ζ ^ p ^ i) ^ (k : ℕ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [MulMemClass.coe_mul, mul_assoc]
        rw [h2, hz i hi, mul_zero, norm_zero]
        exact zero_le_one) j
      have h3 : ((p : K)⁻¹ * (c j)⁻¹) * c j = (p : K)⁻¹ := by
        rw [mul_assoc, inv_mul_cancel₀ hcj, mul_one]
      simp only [h3] at h1
      have h5 : (((p : K)⁻¹ : K) : PadicAlgCl p) = (p : PadicAlgCl p)⁻¹ := by simp
      rw [h5, norm_inv, norm_p] at h1
      rw [inv_inv] at h1
      have h4 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      linarith
    simp [hc0]

  haveI hQf : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI hKQf : FiniteDimensional ℚ_[p] (KQ p K r) := inferInstanceAs (FiniteDimensional ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI hLf : FiniteDimensional ℚ_[p] (Kn p K (r / Nat.gcd f r)) :=
    finiteDimensional_Kn p K hK (Nat.div_pos (Nat.gcd_le_right _ hr) (Nat.gcd_pos_of_pos_right _ hr))
  have dim : Module.finrank ℚ_[p] (KQ p K r) =
      Module.finrank ℚ_[p] (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r)) := by
    have h1 : Module.finrank ℚ_[p] (KQ p K r) = Module.finrank ℚ_[p] K * Module.finrank ℚ_[p] (Qr p r) :=
      Module.finrank_tensorProduct (R := ℚ_[p]) (S := ℚ_[p]) (M := K) (M' := Qr p r)
    rw [h1, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      finrank_Kn p K hK (Nat.div_pos (Nat.gcd_le_right _ hr) (Nat.gcd_pos_of_pos_right _ hr)),
      finrank_Kn p (Q0 p) inferInstance hr, IntermediateField.finrank_bot]
    have h2 : Nat.gcd f r * (r / Nat.gcd f r) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right f r)
    calc _ = Module.finrank ℚ_[p] K * (Nat.gcd f r * (r / Nat.gcd f r)) := by rw [h2, mul_one]
      _ = _ := by ring
  have bij : Function.Bijective (eMap p K hq r) := by
    refine ⟨inj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim (f := (eMap p K hq r).toLinearMap)).1 inj
  obtain ⟨τ, hτK, hτm, hτQ⟩ := GlobalTheory.T.exists_frobenius_automorphism_gcd p K hK f r hq hr
  let e0 := AlgEquiv.ofBijective (eMap p K hq r) bij
  have he : ∀ x i, e0 x i = comp p K hq r i x := fun x i => rfl
  have hlast : ∀ x : KQ p K r, comp p K hq r (Nat.gcd f r) x = τ (comp p K hq r 0 x) := by
    have h : ∀ y : K ⊗[ℚ_[p]] Qr p r, comp p K hq r (Nat.gcd f r) y = τ (comp p K hq r 0 y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero =>
        have z1 : comp p K hq r (Nat.gcd f r) (0 : K ⊗[ℚ_[p]] Qr p r) = 0 := map_zero _
        have z2 : comp p K hq r 0 (0 : K ⊗[ℚ_[p]] Qr p r) = 0 := map_zero _
        rw [z1, z2, map_zero]
      | tmul a b =>
        have h1 : comp p K hq r (Nat.gcd f r) (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) =
            incK p K _ a * incQ p K hq r ((frobQ p r ^ Nat.gcd f r) b) :=
          Algebra.TensorProduct.productMap_apply_tmul _ _ a b
        have h2 : comp p K hq r 0 (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) = incK p K _ a * incQ p K hq r b :=
          (Algebra.TensorProduct.productMap_apply_tmul _ _ a b).trans
            (by rw [AlgHom.comp_apply, pow_zero, AlgHom.one_apply])
        rw [h1, h2, map_mul, hτQ, (hτK _).2 (by rw [coe_incK]; exact a.2)]
      | add y z hy hz =>
        have e1 : comp p K hq r (Nat.gcd f r) (y + z) =
            comp p K hq r (Nat.gcd f r) y + comp p K hq r (Nat.gcd f r) z := map_add _ _ _
        have e2 : comp p K hq r 0 (y + z) = comp p K hq r 0 y + comp p K hq r 0 z := map_add _ _ _
        rw [e1, e2, map_add, hy, hz]
    exact h
  refine ⟨e0.toRingEquiv, τ, hτK, hτm, ?_, ?_, ?_, ?_⟩
  · intro a i
    show ((e0 (inclK p K r a) i : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = a
    rw [he, comp_inclK]
  · intro x i h
    show e0 (sigKQ p K r x) i = e0 x ⟨i.val + 1, h⟩
    rw [he, he, comp_sigKQ]
  · intro x i hi i0 hi0
    show e0 (sigKQ p K r x) i = τ (e0 x i0)
    rw [he, he, comp_sigKQ, hi, hi0, hlast]
  · intro x
    show x ∈ intKQ p K r ↔ ∀ i, e0 x i ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)
    constructor
    · intro hx i
      rw [he]
      exact comp_mem_intR p K hq r i x hx
    · intro h
      obtain ⟨c, rfl⟩ := GlobalTheory.T.unramified_extension_basis p K r hr ζ' hζ x
      have hc : ∀ j, ‖(c j : PadicAlgCl p)‖ ≤ 1 := key c (fun i hi => by
        rw [← val c i, ← mem_intR_iff p K (r / Nat.gcd f r)]
        have h1 := h ⟨i, hi⟩
        rwa [he] at h1)
      have hζi : ζ' ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
        rw [mem_intR_iff p (Q0 p) r]
        exact (UnramifiedExtensions.norm_eq_one_of_pow hN0 hζ.pow_eq_one).le
      apply Subring.sum_mem
      intro j _
      apply Subring.mul_mem
      · apply Subring.subset_closure
        left
        exact ⟨⟨c j, mem_Obar_iff.2 (hc j)⟩, rfl⟩
      · apply Subring.pow_mem
        apply Subring.subset_closure
        right
        exact ⟨⟨ζ', hζi⟩, rfl⟩

end GlobalTheory.LKRes.ResSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VPNeZeroCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VecNeCore

theorem thetaVector_ne_zero_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i, VStd D i → R.vP i A.μ0 ≠ 0 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i _
  exact GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hC.thP.vP i A.μ0)

end GlobalTheory.AdTh.VecNeCore
end

