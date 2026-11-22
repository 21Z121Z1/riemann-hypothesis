import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplittingFw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondInclusionProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0453
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0455
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
import Formalism.LocalToGlobal.Divisibility.Tuples

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLaRingOfIntegers
section
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

theorem Datum.finrank_La_ringOfIntegers :
    ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p),
      letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O);
      Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
  intro p _ D
  letI iL : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  letI iV : Module (𝓞 D.F) D.VF := Module.compHom D.VF (algebraMap (𝓞 D.F) D.F)
  haveI : IsScalarTower (𝓞 D.F) D.F D.VF :=
    ⟨fun c x v => by
      show (algebraMap (𝓞 D.F) D.F c * x) • v = algebraMap (𝓞 D.F) D.F c • (x • v)
      rw [mul_smul]⟩
  let f : D.La →ₗ[𝓞 D.F] D.VF :=
    { toFun := fun z => (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF)
      map_add' := fun z w => TensorProduct.tmul_add _ _ _
      map_smul' := fun c z => by
        rw [RingHom.id_apply]
        show (((1 : ℚ) ⊗ₜ (algebraMap (𝓞 D.F) D.O c • z) : D.VQ) : D.VF) =
          algebraMap (𝓞 D.F) D.F c • (show D.VF from (1 : ℚ) ⊗ₜ z)
        rw [D.smul_VF, show algebraMap (𝓞 D.F) D.F c = (c : D.F) from rfl, D.actF_coe, D.coe_actInt]
        rfl }
  have hf : ∀ z, f z = (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF) := fun _ => rfl

  have hnat : ∀ (n : ℕ) (v : D.VF), ((n : 𝓞 D.F)) • v = n • v := by
    intro n v
    show algebraMap (𝓞 D.F) D.F (n : 𝓞 D.F) • v = n • v
    rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have hloc : IsLocalizedModule (nonZeroDivisors (𝓞 D.F)) f := by
    constructor
    · rintro ⟨c, hc⟩
      have hc0 : (c : D.F) ≠ 0 := by
        intro h
        exact (mem_nonZeroDivisors_iff_ne_zero.1 hc) (by exact_mod_cast h)
      rw [Module.End.isUnit_iff]
      constructor
      · intro v w h
        have h' : (c : D.F) • v = (c : D.F) • w := h
        exact smul_right_injective D.VF hc0 h'
      · intro v
        refine ⟨(c : D.F)⁻¹ • v, ?_⟩
        show (c : D.F) • ((c : D.F)⁻¹ • v) = v
        rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    · intro y
      obtain ⟨q, z, -, hy⟩ := D.exists_tmul y
      have hd : ((q.den : ℕ) : 𝓞 D.F) ∈ nonZeroDivisors (𝓞 D.F) :=
        mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast q.den_ne_zero)
      refine ⟨(q.num • z, ⟨_, hd⟩), ?_⟩
      show ((q.den : ℕ) : 𝓞 D.F) • y = f (q.num • z)
      rw [hnat, hf, hy]
      show q.den • (q ⊗ₜ z : D.VQ) = ((1 : ℚ) ⊗ₜ (q.num • z) : D.VQ)
      rw [TensorProduct.smul_tmul', nsmul_eq_mul, Rat.den_mul_eq_num, ← TensorProduct.smul_tmul,
        zsmul_eq_mul, mul_one]
    · intro z w h
      rw [hf, hf] at h
      obtain ⟨⟨c, hc⟩, hcz⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ)
        (TensorProduct.mk ℤ ℚ D.La 1)).1 h
      have hc0 : ((c : ℤ) : 𝓞 D.F) ≠ 0 := by
        exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.1 hc
      refine ⟨⟨_, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩
      show algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • z = algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • w
      rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact hcz
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 D.F)) f le_rfl
  have h2 := IsFractionRing.finrank_right_eq (𝓞 D.F) D.F D.VF
  rw [← h1, ← h2, D.finrank_VF]

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassEqZeroOfUnitTrivialization
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.PStep

noncomputable section
namespace GlobalTheory.EtC.ChartChern
open CochainComplex CochainComplex.HomComplex GlobalTheory.EtC.ClsSpec GlobalTheory.EtC.ChernSpec

set_option backward.isDefEq.respectTransparency false

theorem firstChernClass_eq_zero_of_unit_trivialization (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : Inv q E)
    (s : ∀ U : Scheme.{0}, Sx E 0 U → (Γ(U, ⊤))ˣ)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 0 U), s V (x.res g) = umap g (s U x))
    (hL : ∀ (U : Scheme.{0}) (x : Sx E 1 U), s U (x.face 1) = lineUnit L x * s U (x.face 0)) :
    c1 q L = 0 := by
  obtain ⟨γ, hγ, h0, h1, h2s⟩ := firstChernClassTateTwist_cocycle_representative q hE L
  have h2 := face_forms q L γ.1 h2s
  have hq0 : ∀ (U : Scheme.{0}) (_ : Sx E 0 U), IsUnit (q : Γ(U, ⊤)) := fun U x ↦ hE U ⟨x⟩
  have e2 : (2 : ℤ).negOnePow = 1 := Int.negOnePow_even 2 even_two
  rw [← hγ, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff γ 1 (by norm_num)]
  rcases kumT_cases q with ht | ht
  ·
    obtain ⟨a, ha_res, ha_d, ha⟩ := exists_d_family ht (p := 0) hq0 s hs
    obtain ⟨b, hb_res, hb⟩ := exists_two_family ht (p := 1) (fun U y ↦ hq0 U (y.face 0))
      (fun U y ↦ lineUnit L y) (fun U y ↦ s U (y.face 0)) (fun V U g y ↦ lineUnit_res L g y)
      (fun V U g y ↦ by rw [← face_res, hs])
    obtain ⟨β₀, hβ₀, hβ₀'⟩ := exists_single (E := E) (I := res _ (tw q 1)) (n := 1) 0 1 (by simp)
      (fun U x ↦ -a U x) (fun V U g x ↦ by rw [← ha_res]; exact map_neg _ _)
    obtain ⟨β₁, hβ₁, hβ₁'⟩ := exists_single (E := E) (I := res _ (tw q 1)) (n := 1) 1 0 (by simp)
      b hb_res
    have K0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U),
        ev (δ 1 2 (β₀ + β₁)) 0 2 (by simp) U x = ev γ.1 0 2 (by simp) U x := by
      intro U x
      rw [CupSpec.ev_δ_zero (by norm_num) _ U 1 2 (by simp) (by simp) x, h0, ClsSpec.ev_add, hβ₀,
        hβ₁' 0 1 (by simp) U x (by norm_num), add_zero]
      have hd := ha_d U x
      simp only [Sec.map] at hd ⊢
      rw [map_neg, hd, neg_zero]
    have K1' : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
        w ^ q = s U (x.face 0) →
        ev (δ 1 2 (β₀ + β₁)) 1 1 (by simp) U x = ev γ.1 1 1 (by simp) U x := by
      intro U x v w hv hw
      have hvw : (v * w) ^ q = s U (x.face 1) := by rw [mul_pow, hv, hw, hL]
      rw [CupSpec.ev_δ_succ (by norm_num) _ U 0 0 1 (by simp) (by simp) x, h1 U x v hv,
        ClsSpec.ev_add, hβ₀' 1 0 (by simp) U x (by norm_num), hβ₁, smap_add, smap_zero, zero_add]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, ClsSpec.ev_add, hβ₀, hβ₁',
        Fin.succ_zero_eq_one, ne_eq, zero_ne_one, not_false_eq_true]
      rw [hb U x v w hv hw, ha U _ w hw, ha U _ (v * w) hvw, e2]
      simp only [smap_add, smap_sub, add_zero, one_smul, Fin.val_zero, Fin.val_one,
        pow_zero, pow_one, neg_smul, neg_neg]
      abel
    have K1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U),
        ev (δ 1 2 (β₀ + β₁)) 1 1 (by simp) U x = ev γ.1 1 1 (by simp) U x := by
      intro U x
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (ClsSpec.loc_and (root_loc (hq0 U (x.face 0)) (lineUnit L x))
        (root_loc (hq0 U (x.face 0)) (s U (x.face 0)))) ?_
      rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
      rw [CupSpec.ev_res, CupSpec.ev_res]
      exact K1' V (x.res g) v w (by rw [hv, lineUnit_res]) (by rw [hw, ← face_res, hs])
    have K2' : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w z : (Γ(U, ⊤))ˣ),
        v ^ q = lineUnit L (x.face 2) → w ^ q = lineUnit L (x.face 0) →
        z ^ q = s U ((x.face 0).face 0) →
        ev (δ 1 2 (β₀ + β₁)) 2 0 (by simp) U x = ev γ.1 2 0 (by simp) U x := by
      intro U x v w z hv hw hz
      have f10 : (x.face 1).face 0 = (x.face 0).face 0 :=
        face_face x 1 0 0 0 (SimplexCategory.δ_comp_δ (i := 0) (j := 0) le_rfl)
      have f20 : (x.face 2).face 0 = (x.face 0).face 1 :=
        face_face x 2 0 0 1 (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide))
      have hvw : (v * w) ^ q = lineUnit L (x.face 1) := by rw [mul_pow, hv, hw, lineUnit_face]
      have hz1 : z ^ q = s U ((x.face 1).face 0) := by rw [f10, hz]
      have hwz : (w * z) ^ q = s U ((x.face 2).face 0) := by rw [mul_pow, hw, hz, f20, hL]
      rw [CupSpec.ev_δ_succ (by norm_num) _ U 1 (-1) 0 (by simp) (by simp) x, h2 U x v w hv hw]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, ClsSpec.ev_add, hβ₀', hβ₁,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two, ne_eq, one_ne_zero, not_false_eq_true]
      rw [hb U _ w z hw hz, hb U _ (v * w) z hvw hz1, hb U _ v (w * z) hv hwz, e2, mul_assoc]
      simp only [zero_add, add_zero, one_smul, Fin.val_zero, Fin.val_one, Fin.val_two,
        pow_zero, pow_one, neg_smul]
      simp only [even_two, Even.neg_one_pow, one_smul]
      rw [hβ₀' 2 (-1) (by simp) U x (by norm_num), hβ₁' 2 (-1) (by simp) U x (by norm_num), add_zero,
        smap_zero, zero_add]
      abel
    have K2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U),
        ev (δ 1 2 (β₀ + β₁)) 2 0 (by simp) U x = ev γ.1 2 0 (by simp) U x := by
      intro U x
      have hU := hq0 U ((x.face 0).face 0)
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (ClsSpec.loc_and (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2)))
        (root_loc hU (lineUnit L (x.face 0)))) (root_loc hU (s U ((x.face 0).face 0)))) ?_
      rintro V g ⟨⟨⟨v, hv⟩, ⟨w, hw⟩⟩, ⟨z, hz⟩⟩
      rw [CupSpec.ev_res, CupSpec.ev_res]
      exact K2' V (x.res g) v w z (by rw [hv, ← face_res, lineUnit_res])
        (by rw [hw, ← face_res, lineUnit_res]) (by rw [hz, ← face_res, ← face_res, hs])
    refine ⟨β₀ + β₁, CupSpec.ev_ext _ _ fun p t ht' U x ↦ ?_⟩
    rcases p with _ | _ | _ | p
    · obtain rfl : t = 2 := by omega
      exact K0 U x
    · obtain rfl : t = 1 := by omega
      exact K1 U x
    · obtain rfl : t = 0 := by omega
      exact K2 U x
    · exact ChernSpec.sec_neg _ t (by omega) _ _
  ·
    have Z1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U), (0 : Sec ((res _ (tw q 1)).X 1) U) =
        ev γ.1 1 1 (by simp) U x := by
      intro U x
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (root_loc (hq0 U (x.face 0)) (lineUnit L x)) ?_
      rintro V g ⟨v, hv⟩
      rw [CupSpec.ev_res, res_zero, h1 V (x.res g) v (by rw [hv, lineUnit_res]), ht]
      simp only [Pi.zero_apply, smap_zero]
    have Z2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U), (0 : Sec ((res _ (tw q 1)).X 0) U) =
        ev γ.1 2 0 (by simp) U x := by
      intro U x
      have hU := hq0 U ((x.face 0).face 0)
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2)))
        (root_loc hU (lineUnit L (x.face 0)))) ?_
      rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
      rw [CupSpec.ev_res, res_zero, h2 V (x.res g) v w (by rw [hv, ← face_res, lineUnit_res])
        (by rw [hw, ← face_res, lineUnit_res]), ht]
      simp only [Pi.zero_apply, add_zero, sub_zero]
    refine ⟨0, ?_⟩
    rw [δ_zero]
    refine CupSpec.ev_ext _ _ fun p t ht' U x ↦ ?_
    rw [CupSpec.ev_zero]
    rcases p with _ | _ | _ | p
    · obtain rfl : t = 2 := by omega
      exact (h0 U x).symm
    · obtain rfl : t = 1 := by omega
      exact Z1 U x
    · obtain rfl : t = 0 := by omega
      exact Z2 U x
    · exact ChernSpec.sec_neg _ t (by omega) _ _

def vtx {N : ℕ} {U : Scheme.{0}} (x : Sx (ofCat (tuCat (N + 1) (lastU N) (lastU_map N))) 0 U) :
    TU (N + 1) (lastU N) Γ(U, ⊤) :=
  (show ComposableArrows (TU (N + 1) (lastU N) Γ(U, ⊤)) 0 from x).obj 0

def lastUnit {N : ℕ} {U : Scheme.{0}} (x : Sx (ofCat (tuCat (N + 1) (lastU N) (lastU_map N))) 0 U) : (Γ(U, ⊤))ˣ :=
  (vtx x).2.unit

end GlobalTheory.EtC.ChartChern

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierIntertwinesSiegelLeviOperator
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem blocks_of_weyl_mul_eq {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
    {ν : Type} [Fintype ν] [DecidableEq ν] {p q : UG c (stdJ ν E)} (hp : p ∈ sieg c ν) (hq : q ∈ sieg c ν)
    (h : weyl c ν * p = q * weyl c ν) :
    (mat c p).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₁ = (mat c p).toBlocks₂₂ := by
  have h1 : stdJ ν E * mat c p = mat c q * stdJ ν E := congrArg (mat c) h
  rw [← fromBlocks_toBlocks (mat c p), ← fromBlocks_toBlocks (mat c q), (mem_sieg c).mp hp, (mem_sieg c).mp hq,
    stdJ, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h1
  obtain ⟨h11, h12, -, h22⟩ := h1
  refine ⟨?_, ?_, ?_⟩
  · simpa using h22
  · simpa using h11
  · simpa using h12.symm

theorem fou_parFun_levi : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, weyl c ν * p = q * weyl c ν → ∀ φ : Matrix α ν E → ℂ, fou c ψ Q μ (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c q) (fou c ψ Q μ φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ _ _ χ _ hχ _ _ μ _ p hp q hq hpq φ
  obtain ⟨hb, hb', ha'⟩ := blocks_of_weyl_mul_eq c hp hq hpq
  obtain ⟨had, -, -⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν p hp
  obtain ⟨β, hβ, -, -, hadj, -⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  obtain ⟨-, -, -, -, hsc, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hχ
  obtain ⟨-, hring, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  set a := (mat c p).toBlocks₁₁ with ha
  set d := (mat c p).toBlocks₂₂ with hd
  have hda : (d.map c)ᵀ * a = 1 := mul_eq_one_comm.mp had
  let A : GL ν E := ⟨a, (d.map c)ᵀ, had, hda⟩
  have hmap := GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt F E c δ hE α ν μ 1 A
  simp only [Units.val_one, Matrix.one_mul, map_one, one_pow, one_mul] at hmap
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun y => y * a
      invFun := fun y => y * (d.map c)ᵀ
      left_inv := fun y => by simp only [Matrix.mul_assoc, had, Matrix.mul_one]
      right_inv := fun y => by simp only [Matrix.mul_assoc, hda, Matrix.mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  have hdet : d.det = (c a.det)⁻¹ := by
    have h1 : a.det * c d.det = 1 := by
      have := congrArg Matrix.det had
      rw [det_mul, det_transpose, det_one] at this
      rw [← this]
      congr 1
      exact RingHom.map_det (c : E →+* E) d
    have h2 := congrArg c h1
    rw [map_mul, hE.invol, map_one] at h2
    exact eq_inv_of_mul_eq_one_right h2
  have hsc' := hsc (Matrix.GeneralLinearGroup.det A)
  have hAdet : ((Matrix.GeneralLinearGroup.det A : Eˣ) : E) = a.det := rfl
  rw [hAdet, ← hdet] at hsc'
  have hN : nabs F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det A)) ≠ 0 :=
    (NNReal.coe_pos.mpr distribHaarChar_pos).ne'
  funext x
  have h0 : ∀ y : Matrix α ν E, pr c Q y 0 = 0 := fun y => by rw [← hβ, map_zero]
  have hint : ∫ y, ψ (pr c Q (x * d) (y * a)) * φ (y * a) ∂μ
      = (((nabs F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det A)) ^ Fintype.card α : ℝ) : ℂ))⁻¹
        * ∫ y, ψ (pr c Q (x * d) y) * φ y ∂μ := by
    have h1 := integral_map_equiv (μ := μ) e.toMeasurableEquiv (fun y => ψ (pr c Q (x * d) y) * φ y)
    have h2 : μ.map e.toMeasurableEquiv = _ := hmap
    rw [h2, integral_smul_nnreal_measure] at h1
    refine Eq.trans h1.symm ?_
    rw [NNReal.smul_def, Complex.real_smul]
    simp [nabs]
  have hpr : ∀ y : Matrix α ν E, pr c Q (x * d) (y * a) = pr c Q x y := fun y => by
    rw [← hβ, hadj, Matrix.mul_assoc, had, Matrix.mul_one, hβ]
  simp only [hpr] at hint
  simp only [fou, four, parFun, hb, hb', ha', ← ha, ← hd, Matrix.mul_zero, h0, mul_zero, AddChar.map_zero_eq_one, one_mul]
  simp only [mul_left_comm _ (sc F χ (Fintype.card α) a.det)]
  rw [integral_const_mul, hint, ← hsc', ← mul_assoc, mul_assoc (sc F χ _ d.det), mul_inv_cancel₀, mul_one]
  exact_mod_cast pow_ne_zero _ hN

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeGeneratorTopForm
section
open GlobalTheory GlobalTheory.TopForm

namespace GlobalTheory

open KaehlerDifferential IsLocalRing Module

theorem isFreeGen_dForm_uniformiser_cons : ∀ (k V : Type) [Field k] [CharZero k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (α : k →+* V) (n : ℕ) (t : V) (w : Fin n → V), α.EssFiniteType →
    Irreducible t → Nonempty (Module.Basis (Fin (n + 1)) V (Omega α)) →
    (∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ α w P)) →
    IsFreeGen V (dForm α (Fin.cons t w : Fin (n + 1) → V)) := by
  intro k V _ _ _ _ _ α n t w hft ht hb₀ hw
  obtain ⟨b₀⟩ := hb₀
  letI := α.toAlgebra
  haveI : Algebra.EssFiniteType k V := hft
  haveI : Algebra.FormallySmooth k V := formallySmooth_of_isRegularLocalRing_of_perfectField k V
  let κ := ResidueField V
  let wb : Fin n → κ := fun i => algebraMap V κ (w i)

  have hai : AlgebraicIndependent k wb := by
    rw [algebraicIndependent_iff]
    intro P hP
    by_contra hne
    have hu := hw P hne
    have e : MvPolynomial.aeval wb P = algebraMap V κ (MvPolynomial.eval₂ α w P) := by
      rw [show wb = algebraMap V κ ∘ w from rfl, MvPolynomial.aeval_algebraMap_apply]
      rfl
    rw [e] at hP
    exact (residue_ne_zero_iff_isUnit _).mpr hu hP

  have hdli : LinearIndependent κ fun i => D k κ (wb i) := by
    have hs : AlgebraicIndepOn k id (Set.range wb) := by
      exact (algebraicIndependent_subtype_range hai.injective).mpr hai
    obtain ⟨s, hsub, hs⟩ := exists_isTranscendenceBasis_superset hs
    haveI := hs.isAlgebraic_field
    haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → κ))) κ :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨b, hb⟩ := exists_basis_kaehler_of_algebraicIndependent hs.1
    let ι : Fin n → s := fun i => ⟨wb i, hsub (Set.mem_range_self i)⟩
    have hι : Function.Injective ι := fun i j h => hai.injective (congrArg Subtype.val h)
    have := b.linearIndependent.comp ι hι
    convert this using 1
    funext i
    simp [ι, hb]
  have ht₀ : algebraMap V κ t = 0 := (residue_eq_zero_iff t).mpr (by
    rw [ht.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self t)
  let z : Fin (n + 1) → V := Fin.cons t w
  have hli : LinearIndependent κ (TensorProduct.mk V κ Ω[V⁄k] 1 ∘ fun i => D k V (z i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [Function.comp_apply, TensorProduct.mk_apply, z, Fin.cons_zero, Fin.cons_succ] at hg
    have hφ := congrArg (mapBaseChange k V κ) hg
    simp only [map_add, map_sum, map_smul, map_zero, mapBaseChange_tmul, one_smul, map_D, ht₀,
      Derivation.map_zero, smul_zero, zero_add] at hφ
    have hs : ∀ i : Fin n, g i.succ = 0 :=
      Fintype.linearIndependent_iff.mp hdli (fun i => g i.succ) hφ
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have h0 : g 0 = 0 := by
      rcases smul_eq_zero.mp hg with h | h
      · exact h
      · exact absurd h (one_tmul_D_ne_zero k ht)
    intro i
    exact Fin.cases h0 hs i
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis (b₀.baseChange κ), Fintype.card_fin])
  haveI : Module.Free V Ω[V⁄k] := Module.Free.of_basis b₀
  haveI : Module.Finite V Ω[V⁄k] := Module.Finite.of_basis b₀
  haveI : Module.FinitePresentation V Ω[V⁄k] := Module.finitePresentation_of_finite V _
  obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange (R := V) (fun i => D k V (z i)) hli hsp
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal V).subtype
      Subtype.val_injective)
  exact isFreeGen_dForm z b hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePuncturedStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_of_etale_on_punctured_spectrum : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 3 ≤ ringKrullDim R → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Module.Free R A := by
  first | exact @GlobalTheory.PurityStep.free_of_etale_punctured | exact GlobalTheory.PurityStep.free_of_etale_punctured | (intros; apply GlobalTheory.PurityStep.free_of_etale_punctured <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZeroStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionField_finite_support_sum_order_eq_zero : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ x : F, x ≠ 0 → {v : Place k F | v.1 x ≠ 1}.Finite ∧ ∑ᶠ v : Place k F, ord v x = 0 := by
  first | exact @GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero | exact GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero | (intros; apply GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceLocalIndexColengthStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldPlace_local_index_colength : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (h : Matrix (Fin n) (Fin n) F), h.det ≠ 0 → (∀ i j, v.1 (h⁻¹ i j) ≤ 1) → ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = -ord v h.det ∧ ∀ x : Fin n → F, (∀ i, v.1 (x i) ≤ 1) → φ x = 0 → ∀ i, v.1 (h.mulVec x i) ≤ 1 := by
  first | exact @GlobalTheory.Nef.local_index | exact GlobalTheory.Nef.local_index | (intros; apply GlobalTheory.Nef.local_index <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenFunctionCharacterSum
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.green_function_character_sum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) (S : F[X] → ℂ), 0 < m → ((Nat.card F : ℂ) ^ m - 1) * ∑ᶠ x, psiG (rootSum θ k) m x * star (chG S m x) = (Nat.card (GL (Fin m) F) : ℂ) * ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ m - 1) = 1}, θ α ^ k * star (S (minpoly F α ^ (m / (minpoly F α).natDegree))) := by
  first | (exact @GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus) | (exact GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus) | (intros; apply GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoTermIteratedFDerivSummableBoundStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F),
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ, Summable u ∧
      ∀ p, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z p.1.out.1 p.2.1) z‖ ≤ u p := by
  first | exact @GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound | exact GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound | (intros; apply GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityOfPrincipalCongruenceStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invAlg_identity_of_principal_congruence : UnitLemmaLie → ∀ (K : UQ) (a : K.O), K.Small a → ∀ B₁ B₂ : InvAlg K, (1 + algebraMap K.O B₁.A a * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A a * B₁.g) = 1 → (1 + algebraMap K.O B₂.A a * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A a * B₂.g) = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence | exact GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence | (intros; apply GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveEtaleSheafOfLinearMapsFromModuleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule : ∀ (R : Type) [CommRing R] (J : Shv R) [Injective J] (M : ModuleCat.{1} (ULift.{1} R)) [Projective M], Injective ((homSh J).obj (op M)) := by
  first | (exact @GlobalTheory.EtC.homSh_injective) | (exact GlobalTheory.EtC.homSh_injective) | (intros; apply GlobalTheory.EtC.homSh_injective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitsFiniteCosetsStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_units_finite_cosets : ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N →
    ∃ S : Finset (AfE ℚ L)ˣ, ∀ k ∈ intU ℚ L, ∃ s ∈ S, s⁻¹ * k ∈ congN ℚ L N := by
  first | exact @GlobalTheory.congN_finite_index | exact GlobalTheory.congN_finite_index | (intros; apply GlobalTheory.congN_finite_index <;> assumption)
end

