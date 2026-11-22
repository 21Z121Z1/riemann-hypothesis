import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignCompatibleNumberingOfWittTowerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexUniformizerPowMulIntegersEqSqPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.UnramIntIndex

theorem le_exp_neg_one_of_lt_one {a : WithZero (Multiplicative ℤ)} (ha : a < 1) :
    a ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne a 0 with rfl | h
  · exact zero_le'
  · obtain ⟨m, rfl⟩ := WithZero.ne_zero_iff_exists.mp h
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at ha
    rw [WithZero.coe_le_coe]
    have h1 : Multiplicative.toAdd m < 0 := ha
    show Multiplicative.toAdd m ≤ -1
    omega

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_maximalIdeal_iff (y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :
    y ∈ IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring ↔
      Valued.v (y : L) < 1 := by
  have hy : Valued.v (y : L) ≤ 1 := y.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hn
    refine lt_of_le_of_ne hy fun h1 => hn ?_
    have h0 : (y : L) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : Valued.v ((y : L)⁻¹) ≤ 1 := by rw [map_inv₀, h1, inv_one]
    refine IsUnit.of_mul_eq_one (⟨(y : L)⁻¹, hinv⟩ : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)
  · rintro hlt ⟨u, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z, (u : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) * z = 1 :=
      ⟨_, u.mul_inv⟩
    have h11 : (((u : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) : L)) * (z : L) = 1 :=
      congrArg Subtype.val hz
    have h1 := congrArg Valued.v h11
    rw [map_mul, map_one] at h1
    have h2 : Valued.v (z : L) ≤ 1 := z.2
    exact absurd h1 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt))

theorem relIndex_mul_uniformizer (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) :
    ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).relIndex
      (Formalism.UG.intL L).toAddSubgroup = q ^ 2 := by
  obtain ⟨-, -, -, h4, -, -, h7⟩ := h
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring with hV
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  have hlt : Valued.v ϖ < 1 := by
    rw [h4, ← WithZero.coe_one, WithZero.coe_lt_coe]
    show (-1 : ℤ) < 0
    omega
  have hI : (IsLocalRing.maximalIdeal V).toAddSubgroup.index = q ^ 2 := h7
  let f : V →+ L := V.subtype.toAddMonoidHom
  have hf : Function.Injective f := Subtype.val_injective
  have e1 : (IsLocalRing.maximalIdeal V).toAddSubgroup.map f =
      (Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ) := by
    ext x
    simp only [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : Valued.v (y : L) < 1 := (mem_maximalIdeal_iff y).1 hy
      have hle := le_exp_neg_one_of_lt_one hy'
      refine ⟨ϖ⁻¹ * (y : L), ?_, ?_⟩
      · show Valued.v (ϖ⁻¹ * (y : L)) ≤ 1
        rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.mpr (by simpa using h0)), mul_one, h4]
        exact hle
      · show ϖ * (ϖ⁻¹ * (y : L)) = (y : L)
        field_simp
    · rintro ⟨o, ho, rfl⟩
      have ho' : Valued.v o ≤ 1 := ho
      have hm : Valued.v (ϖ * o) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' ho') hlt
      exact ⟨⟨ϖ * o, hm.le⟩, (mem_maximalIdeal_iff _).2 hm, rfl⟩
  have e2 : (⊤ : AddSubgroup V).map f = (Formalism.UG.intL L).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← e1, ← e2, AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_top_right]
  exact hI

theorem relIndex_mul_uniformizer_pow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) (e : ℕ) :
    ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex
      (Formalism.UG.intL L).toAddSubgroup = (q ^ 2) ^ e := by
  have hbase := relIndex_mul_uniformizer ϖ c q h
  obtain ⟨-, -, -, h4, -⟩ := h
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  have hϖ : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [h4, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    omega
  set O := (Formalism.UG.intL L).toAddSubgroup with hO
  have hmulle : ∀ a ∈ Formalism.UG.intL L, O.map (AddMonoidHom.mulLeft a) ≤ O := by
    rintro a ha _ ⟨o, ho, rfl⟩
    exact (Formalism.UG.intL L).mul_mem ha ho
  induction e with
  | zero =>
    have : O.map (AddMonoidHom.mulLeft (ϖ ^ 0)) = O := by
      ext x
      simp [AddSubgroup.mem_map]
    rw [this]
    simp
  | succ e ih =>
    have hinj : Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e)) :=
      mul_right_injective₀ (pow_ne_zero e h0)
    have hcomp : O.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) =
        (O.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨o, ho, rfl⟩
        exact ⟨ϖ * o, ⟨o, ho, rfl⟩, by rw [pow_succ, mul_assoc]⟩
      · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
        exact ⟨o, ho, by rw [pow_succ, mul_assoc]⟩
    have hstep : (O.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1)))).relIndex
        (O.map (AddMonoidHom.mulLeft (ϖ ^ e))) = q ^ 2 := by
      rw [hcomp, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
      exact hbase
    have hle1 : O.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) ≤ O.map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      rw [hcomp]
      exact AddSubgroup.map_mono (hmulle ϖ hϖ)
    have hle2 := hmulle (ϖ ^ e) (pow_mem hϖ e)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, hstep, ih]
    exact (pow_succ' _ _).symm

end GlobalTheory.UnramIntIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledTensorLatticeLeCompletedHomLatticeOffPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel.TrOff

section Help
variable {D : D7} {S T : HSp D}

theorem partAt_add (c : AE D) (x y : WO S T) :
    GlobalTheory.LiftLevel.partAt c (x + y) = GlobalTheory.LiftLevel.partAt c x + GlobalTheory.LiftLevel.partAt c y :=
  Matrix.ext fun i j => mul_add c (x i j) (y i j)

theorem partAt_zero (c : AE D) : GlobalTheory.LiftLevel.partAt c (0 : WO S T) = 0 :=
  Matrix.ext fun _ _ => mul_zero c

theorem partAt_neg (c : AE D) (x : WO S T) : GlobalTheory.LiftLevel.partAt c (-x) = -GlobalTheory.LiftLevel.partAt c x :=
  Matrix.ext fun i j => mul_neg c (x i j)

noncomputable def gm (S T : HSp D) (γ : Af D.host.F) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : WO S T :=
  Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a

theorem gm_add (γ : Af D.host.F) (x y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    gm S T γ (x + y) = gm S T γ x + gm S T γ y :=
  Matrix.ext fun a k => TensorProduct.tmul_add _ (x k a) (y k a)

theorem gm_zero (γ : Af D.host.F) : gm S T γ 0 = 0 :=
  Matrix.ext fun a k => TensorProduct.tmul_zero _ _

theorem gm_neg (γ : Af D.host.F) (x : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    gm S T γ (-x) = -gm S T γ x :=
  Matrix.ext fun a k => TensorProduct.tmul_neg _ (x k a)

theorem partAt_gm (σ α : Af D.host.F) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    GlobalTheory.LiftLevel.partAt (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) (gm S T α y) =
      gm S T ((1 - σ) * α) y := by
  refine Matrix.ext fun a k => ?_
  change (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a) =
    (pairA D.host.F 0 ((1 - σ) * α)) ⊗ₜ[D.host.F] y k a
  rw [sub_mul, one_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← TensorProduct.sub_tmul]
  congr 1
  refine Prod.ext ?_ ?_
  · change (0 : Ainf D.host.F) - _ * 0 = 0
    rw [mul_zero, sub_zero]
  · change α - σ * α = (1 - σ) * α
    ring

end Help

theorem mem_stdL_int {E : Type} [Field E] [NumberField E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdL E n ↔ ∀ a, IsIntegral ℤ (v a) := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro a
      show IsIntegral ℤ ((Pi.single b 1 : Fin n → E) a)
      by_cases h : a = b
      · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
      · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
    | zero => intro a; exact isIntegral_zero
    | add x y _ _ hx hy => intro a; exact (hx a).add (hy a)
    | smul c x _ hx => intro a; exact (c.2).mul (hx a)
  · intro h
    have e : v = ∑ a, (⟨v a, h a⟩ : 𝓞 E) • (Pi.single a 1 : Fin n → E) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.smul_apply, Pi.single_eq_same]
        change v i = v i * 1
        rw [mul_one]
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem star_stdL : ∀ (D : D7) (n : ℕ) (v : Fin n → D.host.E), v ∈ stdL D.host.E n ↔ star v ∈ stdL D.host.E n := by
  intro D n v
  rw [mem_stdL_int, mem_stdL_int]
  refine forall_congr' fun a => ?_
  change _ ↔ IsIntegral ℤ (star (v a))
  exact ⟨fun h => h.map (starRingEnd D.host.E).toIntAlgHom, fun h => by
    have := h.map (starRingEnd D.host.E).toIntAlgHom
    rwa [show (starRingEnd D.host.E).toIntAlgHom (star (v a)) = v a from star_star (v a)] at this⟩

theorem rowTriv : ∀ (D : D7) (S T : HSp D) (k₀ : GA D S) (f : AE D), 0 < T.rank → f * f = f → (∀ x : WO S T, IsHalf f x → actO S T k₀ 1 x = x) → ∀ i j, f * (mt S k₀⁻¹ - 1) i j = 0 := by
  intro D S T k₀ f hT hf h i j
  let i₀ : Fin T.rank := ⟨0, hT⟩
  let x : WO S T := Matrix.of fun a b => if a = i₀ ∧ b = i then f else 0
  have hx : IsHalf f x := fun a b => by
    simp only [x, Matrix.of_apply]
    split_ifs
    · exact hf
    · exact mul_zero f
  have h1 := congrFun (congrFun (h x hx) i₀) j
  unfold actO at h1
  rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · simp only [x, Matrix.of_apply, true_and, if_true] at h1
    rw [Matrix.sub_apply, mul_sub, h1, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  · intro b _ hb
    simp [x, hb]
  · intro hi; exact absurd (Finset.mem_univ i) hi

end GlobalTheory.LiftLevel.TrOff

namespace GlobalTheory.LiftLevel

open GlobalTheory.LiftLevel.TrOff in

theorem partAt_off_mem_latO : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' hab hmover hgen hIsMov Lv hLv u hu
  by_cases hT : T.rank = 0
  · have h0 : GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u = 0 := Matrix.ext fun i _ => absurd i.2 (by omega)
    rw [h0]; exact zero_mem _
  have hTpos : 0 < T.rank := Nat.pos_of_ne_zero hT
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := GlobalTheory.T.exists_finiteAdele_of_splitPlaces_idempotentSum D _ e he
  have hf : 1 - e - cA D e = 1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) := by rw [hσ]; ring
  have hgg : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)
      = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) := by
    rw [hσ]; exact (GlobalTheory.IdemConjSum.idemSum_add_conj_idem _ e he).1
  have hff : (1 - e - cA D e) * (1 - e - cA D e) = 1 - e - cA D e := by
    rw [hf]; linear_combination hgg
  have hrow := rowTriv D S T k₀ (1 - e - cA D e) hTpos hff hmover.2.1
  rw [hf] at hrow
  have hstar : ∀ v, v ∈ stdL D.host.E S.rank ↔ star v ∈ stdL D.host.E S.rank := star_stdL D S.rank
  rw [GlobalTheory.Ker.LatTens.latO_eq_hatA D S T C _ _ ΛT C.X.Λ hstar hAA]
  have hO : ∀ (c : 𝓞 D.host.F), ∀ y ∈ tens (stdL D.host.E S.rank) C.X.Λ,
      (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ tens (stdL D.host.E S.rank) C.X.Λ := fun c y hy =>
    GlobalTheory.Ker.HatLat.smul_mem_tens _ _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hy
  have hgen' : ∀ α ∈ intAf D.host.F, ∀ y ∈ tens Λ' (Lv.sh C.X.Λ),
      gm S T ((1 - σ) * α) y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) := by
    intro α hα y hy
    have hγ : (1 - σ) * α ∈ intAf D.host.F := by
      intro w
      rw [map_mul, map_sub, map_one]
      by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
      · obtain ⟨PP, hPP, rfl⟩ := hw
        rw [hσ1 PP hPP, sub_self, zero_mul]; exact zero_mem _
      · push_neg at hw
        rw [hσ0 w hw, sub_zero, one_mul]; exact hα w
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u', hu', rfl⟩ := hy
      refine GlobalTheory.T.mem_completedMatrixGroup_of_local_multiplier D S T _ hO _ hγ _ fun w => ?_
      by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
      · left
        obtain ⟨PP, hPP, rfl⟩ := hw
        rw [map_mul, map_sub, map_one, hσ1 PP hPP, sub_self, zero_mul]
      · right
        push_neg at hw
        obtain ⟨t₁, ht₁, h1⟩ := GlobalTheory.T.exists_multiplier_standard_lattice_of_mover_trivial D S k₀ Λ' σ w (hσ0 w hw) hrow hIsMov v hv
        have hu'' : u' ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) C.X.Λ := by
          have : Lv.sh C.X.Λ = idq Lv.𝔪 (conjI Lv.𝔪) C.X.Λ := rfl
          rw [this, hLv] at hu'; exact hu'
        obtain ⟨t₂, ht₂, h2'⟩ := GlobalTheory.T.exists_multiplier_shifted_lattice_away_from_places D T.rank Pg Q C.X.Λ w hw u' hu''
        refine ⟨t₁ * t₂, fun hm => (w.isPrime.mem_or_mem hm).elim ht₁ ht₂, ?_⟩
        refine AddSubgroup.subset_closure ⟨_, h1, _, h2', ?_⟩
        refine Matrix.ext fun i j => ?_
        change algebraMap D.host.F D.host.E ((t₁ * t₂ : 𝓞 D.host.F) : D.host.F) * (v i * u' j) =
          algebraMap D.host.F D.host.E (t₁ : D.host.F) * v i * (algebraMap D.host.F D.host.E (t₂ : D.host.F) * u' j)
        rw [show ((t₁ * t₂ : 𝓞 D.host.F) : D.host.F) = (t₁ : D.host.F) * (t₂ : D.host.F) from rfl, map_mul]
        ring
    | zero => rw [gm_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [gm_add]; exact add_mem hx hy
    | neg x _ hx => rw [gm_neg]; exact neg_mem hx
  rw [hf]
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    exact (partAt_gm σ α y).symm ▸ hgen' α hα y hy
  | zero => rw [partAt_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [partAt_add]; exact add_mem hx hy
  | neg x _ hx => rw [partAt_neg]; exact neg_mem hx

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeparableCharpolyConstSmul
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.CentralCharSU

attribute [local instance] GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special

theorem separable_charpoly_const_smul {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : B.charpoly.Separable) : (c • B).charpoly.Separable := by
  let q : Polynomial ℂ := Polynomial.C c⁻¹ * Polynomial.X
  have key : (c • B).charpoly = Polynomial.C (c ^ Fintype.card (Fin n)) * B.charpoly.comp q := by
    have h1 : B.charpoly.comp q = (B.charmatrix.map (Polynomial.compRingHom q)).det := by
      have := RingHom.map_det (Polynomial.compRingHom q) B.charmatrix
      rw [Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, this]
      rfl
    rw [h1, Polynomial.C_pow, ← Matrix.det_smul, Matrix.charpoly]
    congr 1
    ext i j : 1
    have hcc : Polynomial.C c * (Polynomial.C c⁻¹ * Polynomial.X) = (Polynomial.X : Polynomial ℂ) := by
      rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul]
    by_cases hij : i = j
    · subst hij
      simp [q, mul_sub, hcc]
    · simp [hij, q]
  have hu : IsUnit (Polynomial.C (c ^ Fintype.card (Fin n))) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hc))
  have hu' : IsUnit (Polynomial.C c⁻¹) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hc))
  have h2 : IsCoprime (B.charpoly.comp q) (B.charpoly.derivative.comp q) :=
    IsCoprime.map h (Polynomial.compRingHom q)
  have hq : Polynomial.derivative q = Polynomial.C c⁻¹ := by simp [q]
  rw [key, Polynomial.separable_def, Polynomial.derivative_C_mul, Polynomial.derivative_comp, hq,
    isCoprime_mul_unit_left_left hu, isCoprime_mul_unit_left_right hu, isCoprime_mul_unit_left_right hu']
  exact h2

theorem isRegSS_central_mul {n : ℕ} {ε : Fin n → Bool} {c : SUJ ε} {ζ : ℂ}
    (hc : suMat ε c = ζ • (1 : Matrix (Fin n) (Fin n) ℂ)) {g : SUJ ε} (hg : IsRegSS (suMat ε g)) :
    IsRegSS (suMat ε (c * g)) := by
  have e : suMat ε (c * g) = ζ • suMat ε g := by
    rw [map_mul, hc, Matrix.smul_mul, Matrix.one_mul]
  by_cases hζ : ζ = 0
  · have h01 : (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      have h := congrArg (· * suMat ε c⁻¹) hc
      simp only [← map_mul, mul_inv_cancel, map_one, hζ, zero_smul, zero_mul] at h
      exact h.symm
    haveI := subsingleton_of_zero_eq_one h01
    rwa [Subsingleton.elim (suMat ε (c * g)) (suMat ε g)]
  · rw [e]
    exact separable_charpoly_const_smul _ ζ hζ hg

theorem continuous_suMat {n : ℕ} (ε : Fin n → Bool) : Continuous (suMat ε) :=
  (isInducing_suMat ε).continuous

theorem charFn_central_mul : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (SUJ ε)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V))
    (h : IsURepOn (SUset ε) π) (Θ : SUJ ε → ℂ), IsCharFn (suMat ε) μ (suRep h) Θ → ∀ (c : SUJ ε) (ζ χ : ℂ),
    suMat ε c = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) → χ ≠ 0 → (∀ v, suRep h c v = χ • v) →
    ∀ g : SUJ ε, IsRegSS (suMat ε g) → Θ (c * g) = χ * Θ g := by
  intro n ε μ _ V _ _ _ π h Θ hΘ c ζ χ hc hχ hv g hg
  haveI := GlobalTheory.DSSU.borelSpace_SUJ ε
  set ρ := suRep h with hρdef
  have hρ : GlobalTheory.OpTrace.IsUnitaryRep ρ := GlobalTheory.Orb.isUnitaryRep_repVia h (suMat_mem ε) (continuous_suMat ε)
  set Θ₂ : SUJ ε → ℂ := fun x => χ⁻¹ * Θ (c * x) with hΘ₂
  have hli : LocallyIntegrable Θ₂ μ := by
    have h0 : LocallyIntegrable (fun x => Θ (c * x)) μ := by
      refine (locallyIntegrable_iff).2 fun K hK => ?_
      have hpre : K = (c * ·) ⁻¹' ((c * ·) '' K) := (Set.preimage_image_eq K (mul_right_injective c)).symm
      rw [hpre]
      exact ((measurePreserving_mul_left μ c).integrableOn_comp_preimage (measurableEmbedding_mulLeft c)).2
        ((locallyIntegrable_iff.1 hΘ.1) _ (hK.image (continuous_mul_left c)))
    exact h0.smul χ⁻¹
  have hcont : ∀ s, IsRegSS (suMat ε s) → ContinuousAt Θ₂ s := fun s hs =>
    continuousAt_const.mul ((hΘ.2.1 (c * s) (isRegSS_central_mul hc hs)).comp (continuous_mul_left c).continuousAt)
  have hΘ₂c : IsCharFn (suMat ε) μ ρ Θ₂ := by
    refine ⟨hli, hcont, fun f hf => ?_⟩
    set f₂ : SUJ ε → ℂ := fun x => f (c⁻¹ * x) with hf₂
    have hf₂m : f₂ ∈ CcMat (suMat ε) := by
      obtain ⟨hs, Φ, hΦ, e⟩ := hf
      refine ⟨hs.comp_homeomorph (Homeomorph.mulLeft c⁻¹), fun x =>
        Φ (fun i j => ∑ k, suMat ε c⁻¹ i k * x k j), ?_, fun x => ?_⟩
      · refine hΦ.comp (contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_)
        exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply_apply ℝ ℂ k j)
      · rw [hf₂]
        simp only [e]
        congr 1
    have hfc : Continuous f := GlobalTheory.Orb.continuous_of_mem_ccSmooth (isInducing_suMat ε).continuous hf
    have hf₂c : Continuous f₂ := GlobalTheory.Orb.continuous_of_mem_ccSmooth (isInducing_suMat ε).continuous hf₂m
    have hop : repOp ρ μ f₂ = χ • repOp ρ μ f := by
      ext v
      rw [hρ.repOp_apply hf₂c hf₂m.1, ContinuousLinearMap.smul_apply, hρ.repOp_apply hfc hf.1, ← hv,
        ← (ρ c).integral_comp_comm (hρ.isRepOp hfc hf.1 v).1,
        ← integral_mul_left_eq_self (fun x => f₂ x • ρ x v) c]
      refine integral_congr_ae (.of_forall fun x => ?_)
      simp [hf₂, map_mul, ContinuousLinearMap.mul_apply]
    have hint : ∫ g, f g * Θ₂ g ∂μ = χ⁻¹ * ∫ g, f₂ g * Θ g ∂μ := by
      rw [← integral_mul_left_eq_self (fun x => f₂ x * Θ x) c, ← integral_const_mul]
      refine integral_congr_ae (.of_forall fun x => ?_)
      simp [hf₂, hΘ₂]
      ring
    have ht := hΘ.2.2 f₂ hf₂m
    rw [hop] at ht
    have he : repOp ρ μ f = χ⁻¹ • (χ • repOp ρ μ f) := by rw [smul_smul, inv_mul_cancel₀ hχ, one_smul]
    rw [he, hint]
    exact ⟨ht.1.smul _, by rw [GlobalTheory.OpTrace.trace_smul, ht.2]⟩
  have hu := GlobalTheory.Orb.IsCharFn.unique (isInducing_suMat ε) hΘ₂c hΘ hg
  simp only [hΘ₂] at hu
  rw [← hu]
  field_simp

end GlobalTheory.CentralCharSU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignCompatibleNumberingOfWittTowerLowerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signCompatibleNumbering_of_wittTower_lower : ∀ (D : D7) (T T' : HSp D) (i : ℕ) (τ : D.what₂.Tau) (fr : Mn T.rank) (ε : Fin T.rank → Bool) (fr' : Mn T'.rank) (ε' : Fin T'.rank → Bool) (r s : ℕ) (e : Ix r s ≃ Fin T.rank), IsWittLower T T' i → frᴴ * Formalism.REAL.Jm ε * fr = gramAt D T τ → IsUnit fr → fr'ᴴ * Formalism.REAL.Jm ε' * fr' = gramAt D T' τ → IsUnit fr' → SignCompat ε e → i ≤ r ∧ i ≤ s ∧ ∃ e' : Ix (r - i) (s - i) ≃ Fin T'.rank, SignCompat ε' e' := by
  first | exact @GlobalTheory.WittSign.signCompat_of_isWittLower | exact GlobalTheory.WittSign.signCompat_of_isWittLower | (intros; apply GlobalTheory.WittSign.signCompat_of_isWittLower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceAdjointMatrix_isCoordinate_equivariant : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord (cA D e) (latO S T ΛS ΛT fun _ => True) (adjCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  first | exact @GlobalTheory.PlaceTensor.adjCo_isCoord | exact GlobalTheory.PlaceTensor.adjCo_isCoord | (intros; apply GlobalTheory.PlaceTensor.adjCo_isCoord <;> assumption)
end

