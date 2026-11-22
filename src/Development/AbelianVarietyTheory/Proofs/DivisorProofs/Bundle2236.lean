import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallScalarReflexIdealSelfDualLattice
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SmallScal

set_option maxHeartbeats 1600000 in

theorem exists_small_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : Coeff l) (n : ℕ) (La : GenLat E n), La.Unimod → ∃ s : c.F, s ≠ 0 ∧ Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c La.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ ∧ ∀ σ : c.F →+* ℂ, ‖σ s‖ ^ 2 * ((La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index : ℝ) ^ (Dw.p + Dw.q) ≤ Real.exp (fieldSz c.F) ^ 2 := by
  intro E _ _ _ H Dw l c n La hU
  haveI : IsTotallyComplex c.F := GlobalTheory.CompHS.isTotallyComplex_coeff c
  obtain ⟨𝔞, h0, h1, h2⟩ := GlobalTheory.BetaEx.exists_index_ideal La.Ln La.La inf_le_left
    (GlobalTheory.BetaEx.bdd_of_unimod La hU) (fun m hm => by
      obtain ⟨a, ha, h⟩ := GlobalTheory.BetaEx.exists_smul_std m
      exact ⟨a, ha, La.La.smul_mem a hm, h⟩)
  set idx : ℕ := (La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index with hidx
  have h2' : Ideal.absNorm 𝔞 = idx := h2
  have hidx0 : idx ≠ 0 := by
    rw [← h2']; exact fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)

  have e : ∀ τ, idealAt c La.Ln τ =
      Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) * idealAt c La.La τ := by
    intro τ
    unfold idealAt
    rw [← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.Ln),
      ← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.La)]
    have := GlobalTheory.BetaEx.span_image_smul (embF c τ) 𝔞 (GlobalTheory.BetaEx.detSpan La.La)
    rw [← h1] at this
    exact this
  let φ : (E →+* ℂ) → (𝓞 E →+* 𝓞 c.F) := fun τ => RingOfIntegers.mapRingHom (embF c τ)
  let B : FractionalIdeal (𝓞 c.F)⁰ c.F :=
    ∏ τ : E →+* ℂ, ((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) ^ Dw.mult τ

  have hS : ∀ τ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ≤
      (((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) := by
    intro τ
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨φ τ a, Ideal.mem_map_of_mem _ ha, rfl⟩
  have hSB : ∏ τ : E →+* ℂ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ ≤
      (B : Submodule (𝓞 c.F) c.F) := by
    have : (B : Submodule (𝓞 c.F) c.F) = FractionalIdeal.coeSubmoduleHom (𝓞 c.F)⁰ c.F B := rfl
    rw [this, map_prod]
    refine Finset.prod_le_prod' fun τ _ => ?_
    rw [map_pow]
    exact pow_le_pow_left' (hS τ) _

  obtain ⟨k, hk⟩ : ∃ k, k = InfinitePlace.nrComplexPlaces c.F := ⟨_, rfl⟩
  have hnF : Module.finrank ℚ c.F = 2 * k := hk ▸ IsTotallyComplex.finrank c.F
  have hnE : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := IsTotallyComplex.finrank E
  have hk0 : k ≠ 0 := by have := Module.finrank_pos (R := ℚ) (M := c.F); omega
  have hdvd : Module.finrank ℚ E ∣ Module.finrank ℚ c.F :=
    (GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ (Classical.arbitrary _)) 𝔞).1
  have hexp : Module.finrank ℚ c.F / Module.finrank ℚ E * ∑ τ : E →+* ℂ, Dw.mult τ = (Dw.p + Dw.q) * k := by
    rw [GlobalTheory.RefSum.sum_mult]
    obtain ⟨t, ht⟩ := hdvd
    have hE0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    rw [ht, Nat.mul_div_cancel_left _ hE0, hnE, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [ht, hnE] at hnF
    have : InfinitePlace.nrComplexPlaces E * t = k := by linarith
    rw [← this]; ring
  have hNB : FractionalIdeal.absNorm B = ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k := by
    simp only [B, map_prod, map_pow, FractionalIdeal.coeIdeal_absNorm]
    simp only [fun τ => (GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ τ) 𝔞).2, h2']
    rw [← pow_mul, ← hexp, pow_mul, Finset.prod_pow_eq_pow_sum]
    push_cast
    ring
  have hX0 : (0 : ℝ) < (idx : ℝ) ^ (Dw.p + Dw.q) := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hidx0) _
  have hB0 : B ≠ 0 := by
    intro hB
    have := hNB
    rw [hB, map_zero] at this
    have h' : ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hidx0))
    exact h' this.symm

  set X : ℝ := (idx : ℝ) ^ (Dw.p + Dw.q) with hXdef
  set R : ℝ := Real.exp (fieldSz c.F) ^ 2 with hR
  have hR0 : 0 < R := by positivity
  have hg : 0 < R / X := div_pos hR0 hX0
  have hcard : Fintype.card (InfinitePlace c.F) = k := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, hk]
  have hd1 : (1 : ℝ) ≤ |(discr c.F : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero c.F)
    exact_mod_cast this
  have hdR : |(discr c.F : ℝ)| ≤ R ^ k := by
    rw [hR, ← pow_mul, ← Real.exp_nat_mul, ← Real.exp_log (lt_of_lt_of_le one_pos hd1)]
    apply Real.exp_le_exp.2
    have hn : (0 : ℝ) < Module.finrank ℚ c.F := by exact_mod_cast Module.finrank_pos
    have hfs := GlobalTheory.CovTop.log_rd_le_fieldSz c.F
    have hlog := Real.log_natCast_nonneg (Module.finrank ℚ c.F)
    have : Real.log |(discr c.F : ℝ)| ≤ (Module.finrank ℚ c.F : ℝ) * fieldSz c.F := by
      rw [div_le_iff₀ hn] at hfs; linarith
    rw [hnF] at this
    push_cast at this ⊢
    linarith
  have hsq : Real.sqrt |(discr c.F : ℝ)| ≤ |(discr c.F : ℝ)| :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hsq0 : 0 < Real.sqrt |(discr c.F : ℝ)| := Real.sqrt_pos.2 (by linarith)
  obtain ⟨b, hb, hb0, hbw⟩ := Formalism.ExtensionFiltration.mk_lt c.F (Units.mk0 B⁻¹ (inv_ne_zero hB0))
    (fun _ => Real.sqrt (R / X)) (fun _ => Real.sqrt_pos.2 hg) (by
      rw [Units.val_mk0, map_inv₀, hNB, Finset.prod_const, Finset.card_univ, hcard, Real.sq_sqrt hg.le, ← hk,
        div_pow]
      push_cast
      rw [← hXdef]
      have hXk : 0 < X ^ k := pow_pos hX0 k
      rw [inv_mul_eq_div, div_mul_eq_mul_div, div_lt_iff₀ hXk, mul_div_assoc', div_mul_cancel₀ _ hXk.ne']
      calc (2 : ℝ) ^ k * Real.sqrt |(discr c.F : ℝ)| < Real.pi ^ k * Real.sqrt |(discr c.F : ℝ)| :=
            mul_lt_mul_of_pos_right (pow_lt_pow_left₀ (by linarith [Real.pi_gt_three]) (by norm_num) hk0) hsq0
        _ ≤ Real.pi ^ k * R ^ k := by gcongr; exact hsq.trans hdR)
  refine ⟨b, hb0, ?_, fun σ => ?_⟩
  ·
    have hsb : Submodule.span (𝓞 c.F) {b} * (B : Submodule (𝓞 c.F) c.F) ≤ 1 := by
      have h1' : Submodule.span (𝓞 c.F) {b} ≤ ((B⁻¹ : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) :=
        Submodule.span_le.2 (Set.singleton_subset_iff.2 hb)
      calc Submodule.span (𝓞 c.F) {b} * (B : Submodule (𝓞 c.F) c.F)
          ≤ ((B⁻¹ : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) * (B : Submodule (𝓞 c.F) c.F) :=
            mul_le_mul' h1' le_rfl
        _ = 1 := by rw [← FractionalIdeal.coe_mul, inv_mul_cancel₀ hB0, FractionalIdeal.coe_one]
    simp only [e, mul_pow, Finset.prod_mul_distrib]
    rw [← mul_assoc]
    calc Submodule.span (𝓞 c.F) {b} * (∏ τ : E →+* ℂ,
            Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ) *
            ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ
        ≤ 1 * ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ :=
          mul_le_mul' ((mul_le_mul' le_rfl hSB).trans hsb) le_rfl
      _ = _ := one_mul _
  ·
    have h1 := hbw (InfinitePlace.mk σ)
    rw [InfinitePlace.apply] at h1
    have h3 : ‖σ b‖ ^ 2 < R / X := (Real.lt_sqrt (norm_nonneg _)).1 h1
    rw [lt_div_iff₀ hX0] at h3
    exact h3.le

end GlobalTheory.SmallScal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallTorsionSetForEndomorphism
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.NeatUnip

theorem iter_comp {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (α : G ⟶ G) (n : ℕ)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) :
    x ≫ (fun f : G ⟶ G => f ≫ α)^[n] (𝟙 G) = (fun z => z ≫ α)^[n] x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [← ih, Category.assoc]

theorem finite_order_unipotent_eq_id : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (α : G ⟶ G) (n m g r : ℕ) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom α → (∀ a, act.act a ≫ α = α ≫ act.act a) → 0 < n → (fun f : G ⟶ G => f ≫ α)^[n] (𝟙 G) = 𝟙 G → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → r + 1 < g → (∃ T : Finset (𝟙_ (Over (Sp k)) ⟶ G), T.card ≤ g ^ r ∧ ∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → x ∈ T) → (∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → (fun z : 𝟙_ (Over (Sp k)) ⟶ G => (z ≫ α) * z⁻¹)^[m] x = 1) → α = 𝟙 G := by
  intro E _ _ k _ _ _ G _ act α n m g r I hG hα hcomm hn hpow hg hI hI2 hr hfin hunip
  classical
  haveI := hG.comm
  haveI := hα
  haveI : ∀ a, IsMonHom (act.act a) := act.hom
  letI cg : CommGroup (𝟙_ (Over (Sp k)) ⟶ G) := Hom.commGroup
  have act0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  letI inst : Module (𝓞 E) (Additive (𝟙_ (Over (Sp k)) ⟶ G)) :=
  { smul := fun a x => Additive.ofMul (x.toMul ≫ act.act a)
    one_smul := fun x => by
      show Additive.ofMul (x.toMul ≫ act.act 1) = x
      rw [act.one, Category.comp_id]; rfl
    mul_smul := fun a b x => by
      show Additive.ofMul (x.toMul ≫ act.act (a * b)) = Additive.ofMul ((x.toMul ≫ act.act b) ≫ act.act a)
      rw [mul_comm a b, act.mul, Category.assoc]
    smul_zero := fun a => by
      show Additive.ofMul ((1 : 𝟙_ (Over (Sp k)) ⟶ G) ≫ act.act a) = Additive.ofMul 1
      rw [MonObj.one_comp]
    smul_add := fun a x y => by
      show Additive.ofMul ((x.toMul * y.toMul) ≫ act.act a) = Additive.ofMul ((x.toMul ≫ act.act a) * (y.toMul ≫ act.act a))
      rw [MonObj.mul_comp]
    add_smul := fun a b x => by
      show Additive.ofMul (x.toMul ≫ act.act (a + b)) = Additive.ofMul ((x.toMul ≫ act.act a) * (x.toMul ≫ act.act b))
      rw [act.add, MonObj.comp_mul]
    zero_smul := fun x => by
      show Additive.ofMul (x.toMul ≫ act.act 0) = Additive.ofMul 1
      rw [act0, MonObj.comp_one] }
  have hsmul : ∀ (a : 𝓞 E) (x : Additive (𝟙_ (Over (Sp k)) ⟶ G)), a • x = Additive.ofMul (x.toMul ≫ act.act a) :=
    fun _ _ => rfl
  have htors : ∀ (J : Ideal (𝓞 E)) (x : 𝟙_ (Over (Sp k)) ⟶ G),
      (∀ a ∈ J, a • Additive.ofMul x = 0) ↔ ∀ a ∈ J, x ≫ act.act a = 1 := fun J x =>
    forall₂_congr fun a _ => by rw [hsmul]; exact ofMul_eq_zero
  let β : Additive (𝟙_ (Over (Sp k)) ⟶ G) →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp k)) ⟶ G) :=
  { toFun := fun x => Additive.ofMul (x.toMul ≫ α)
    map_add' := fun x y => by
      show Additive.ofMul ((x.toMul * y.toMul) ≫ α) = Additive.ofMul ((x.toMul ≫ α) * (y.toMul ≫ α))
      rw [MonObj.mul_comp]
    map_smul' := fun a x => by
      show Additive.ofMul ((x.toMul ≫ act.act a) ≫ α) = Additive.ofMul ((x.toMul ≫ α) ≫ act.act a)
      rw [Category.assoc, hcomm, Category.assoc] }
  have hβ : ∀ x, β x = Additive.ofMul (x.toMul ≫ α) := fun _ => rfl

  let A : AddSubgroup (Additive (𝟙_ (Over (Sp k)) ⟶ G)) :=
  { carrier := {x | ∃ j : ℕ, ∀ a ∈ I ^ j, a • x = 0}
    add_mem' := by
      rintro x y ⟨i, hi⟩ ⟨j, hj⟩
      refine ⟨i + j, fun a ha => ?_⟩
      rw [smul_add, hi a (Ideal.pow_le_pow_right (by omega) ha),
        hj a (Ideal.pow_le_pow_right (by omega) ha), add_zero]
    zero_mem' := ⟨0, fun a _ => smul_zero a⟩
    neg_mem' := by
      rintro x ⟨j, hj⟩
      exact ⟨j, fun a ha => by rw [smul_neg, hj a ha, neg_zero]⟩ }
  have memA : ∀ x, x ∈ A ↔ ∃ j : ℕ, ∀ a ∈ I ^ j, a • x = 0 := fun _ => Iff.rfl
  let βA : A →+ A :=
  { toFun := fun x => ⟨β x.1, by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      exact ⟨j, fun a ha => by rw [← LinearMap.map_smul, hj a ha, map_zero]⟩⟩
    map_zero' := Subtype.ext (map_zero β)
    map_add' := fun x y => Subtype.ext (map_add β x.1 y.1) }
  have hβA : ∀ x : A, ((βA x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) = β x.1 := fun _ => rfl
  have hβAit : ∀ (N : ℕ) (x : A), ((βA^[N] x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) = β^[N] x.1 := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hβA, ih]
  have hβit : ∀ (N : ℕ) (x : Additive (𝟙_ (Over (Sp k)) ⟶ G)),
      β^[N] x = Additive.ofMul ((fun z => z ≫ α)^[N] x.toMul) := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl
  have hsubit : ∀ (N : ℕ) (x : A),
      (((fun z : A => βA z - z)^[N] x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) =
        Additive.ofMul ((fun z : 𝟙_ (Over (Sp k)) ⟶ G => (z ≫ α) * z⁻¹)^[N] (Additive.toMul x.1)) := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', AddSubgroup.coe_sub, hβA, ih, hβ,
        toMul_ofMul, ← ofMul_div, div_eq_mul_inv]
  have hgI : (g : 𝓞 E) ∈ I := hI ▸ Ideal.absNorm_mem I
  have hdivM : ∀ x : Additive (𝟙_ (Over (Sp k)) ⟶ G), ∃ y, g • y = x := by
    intro x
    obtain ⟨y, hy⟩ := GlobalTheory.SS.torusExtension_points_divisible k G (GlobalTheory.TorsionDense.nonempty_torusExtension G hG)
      g hg.one_le x.toMul
    exact ⟨Additive.ofMul y, by rw [← ofMul_pow, hy]; rfl⟩
  obtain ⟨hred1, hred2⟩ := GlobalTheory.T.primaryTorsion_divisible_and_torsion_eq_ideal_torsion E (Additive (𝟙_ (Over (Sp k)) ⟶ G)) g I hg hI hI2 hdivM
  have key := GlobalTheory.T.finiteOrder_unipotent_aut_divisible_primary_eq_id A βA n g r m hn
    (fun x => Subtype.ext (by
      rw [hβAit, hβit, ← iter_comp, hpow, Category.comp_id]; rfl))
    hg (by omega)
    (fun x => by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      obtain ⟨y, hy, hy'⟩ := hred1 j x.1 hj
      exact ⟨⟨y, j + 1, hy'⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact hy)⟩)
    (fun x => by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      refine ⟨j, Subtype.ext ?_⟩
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow]
      exact hj _ (Ideal.pow_mem_pow hgI j))
    (by
      obtain ⟨T, hT, hTm⟩ := hfin
      refine ⟨(T.map Additive.ofMul.toEmbedding).subtype (· ∈ A), ?_, fun x hx => ?_⟩
      · rw [Finset.card_subtype]
        exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_map]; exact hT)
      · have hx' : g • x.1 = 0 := by have := congrArg Subtype.val hx; simpa using this
        obtain ⟨j, hj⟩ := (memA x.1).1 x.2
        have h1 := hred2 j x.1 hj hx'
        rw [Finset.mem_subtype, Finset.mem_map]
        exact ⟨Additive.toMul x.1, hTm _ ((htors I _).1 h1), rfl⟩)
    (fun x hx => by
      have hx' : g • x.1 = 0 := by have := congrArg Subtype.val hx; simpa using this
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      have h1 := hred2 j x.1 hj hx'
      refine Subtype.ext ?_
      have h2 := hunip (Additive.toMul x.1) ((htors I _).1 h1)
      rw [hsubit, h2]; rfl)
  have hfix : ∀ (j : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), (∀ a ∈ I ^ j, x ≫ act.act a = 1) → x ≫ α = x := by
    intro j x hx
    have h := congrArg Subtype.val (key ⟨Additive.ofMul x, j, (htors _ x).2 hx⟩)
    exact congrArg Additive.toMul h
  have hγ : IsMonHom (α * (𝟙 G)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  have hI1 : I ≠ ⊤ := fun h => by
    rw [h, Ideal.absNorm_top] at hI
    exact hg.one_lt.ne hI
  have h1 := GlobalTheory.T.eq_one_of_kills_idealPowerTorsion_semiAbelian E k G act (α * (𝟙 G)⁻¹) I hG hγ
    (fun a => by
      rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.mul_comp, GrpObj.inv_comp, hcomm, Category.comp_id,
        Category.id_comp])
    hI1
    (fun j x hx => by rw [MonObj.comp_mul, GrpObj.comp_inv, hfix j x hx, Category.comp_id, mul_inv_cancel])
  rw [mul_inv_eq_one] at h1
  exact h1

end GlobalTheory.NeatUnip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistingSectionMulLatticeValueLe
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwMulOne

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem val_eq_of_agree {Z : Comp Xo c} {w : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z w)
    {f g : Rul Xo c}
    (h : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c g y = evR Xo c f y) :
    v g = v f := by
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  show nval T.V e (evR Xo c g y.1) = nval T.V e (evR Xo c f y.1)
  rw [h _ y.1 hy.2]

theorem exists_latW_val_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (Z : Comp Xo c)
    (t : TwSec U x Z G₀) (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valOn Z w, ∀ f ∈ latW U G,
    ∃ g ∈ latW U (G + G₀), v g ≤ v f + ((t.hi w - (⌊t.lo w⌋ : ℝ) : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c r U hU x G G₀ hG Z t w v hv f hf
  obtain ⟨f', hres, hlat⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hU Z G f
  have hf'lat := hlat hf
  obtain ⟨a, ha0, hva, hpos⟩ := GlobalTheory.RefSum.ScalApprox.exists_scal c.F t.lo t.finite_lo w
  obtain ⟨φ, hφ, -, hint, -⟩ := GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ t G hG
  have hg := hint a ha0 hpos f' hf'lat (a • φ f') (by rw [Submodule.coe_smul])
  refine ⟨⟨(a • φ f' : cuspOn U Z (G + G₀)), cuspOn_le U Z (G + G₀) (a • φ f').2⟩, (mem_latOn U).1 hg, ?_⟩
  have hV := isVal_valOn hv
  obtain ⟨b, hb, -, -, hbhi⟩ := t.exists_val hv
  have e1 : v (f' : Rul Xo c) = v (f : Rul Xo c) := val_eq_of_agree hv (hres)
  show v ((a • φ f' : cuspOn U Z (G + G₀)) : Rul Xo c) ≤ _
  rw [Submodule.coe_smul, hV.smul _ _ ha0, hφ, hV.mul, e1, hb, hva]
  rw [← add_assoc, add_comm (((-(⌊t.lo w⌋ : ℝ) : ℝ)) : EReal) (v (f : Rul Xo c)), add_assoc, ← EReal.coe_add]
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.2 (by linarith))

end GlobalTheory.TwMulOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFrameReadingNeZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory

theorem exists_rdU_ne_zero_of_mem_secZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (e : Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, F ≠ 0 → ∃ k, ∃ x ∈ (U.X k).dom, rdU U F k x ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ r U hU e F hF hF0
  by_contra hcon
  push_neg at hcon
  apply hF0
  funext p y
  show F p y = 0
  refine Formalism.L2.Pj.eq_zero_of_cpts σ p _ fun ψ => ?_
  obtain ⟨k, x, u, hk⟩ :=
    GlobalTheory.test_value_eq_const_mul_reading_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange U hU e p y ψ
  have h := hk F hF
  rw [hcon k x.1 x.2, mul_zero] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem dualMap_comp_dualMapR {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    (dualMap g).comp (Chart.dualMapR f) = dualMap (g.comp f) := by
  ext a <;> simp [dualMap, Chart.dualMapR]

theorem dualMap_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') :
    (dualMap g).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp g := by
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isPullback_gen {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) :
    IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) A.A.hom G.hom (spMap (algebraMap V (FractionRing V))) := by
  haveI : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
  have sq : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK V)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using Over.w U.gen.inv⟩
  simpa using sq.paste_horiz (IsPullback.of_hasPullback G.hom (jK V))

theorem vecAt_genFibre : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (y : epsR V ⟶ G),
    (∃! yA, VecAt U.toUnifPre F y yA) ∧
    (∃! v : epsR (FractionRing V) ⟶ A.A, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v) ∧
    ∀ (v : epsR (FractionRing V) ⟶ A.A) yA, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v →
      VecAt U.toUnifPre F y yA → yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
  intro V _ _ _ _ _ D A G _ _ _ U F _ _ y
  have hφ := isPullback_gen U.toUnifPre
  have hT : IsPullback (fst (TFK (R := V) F) A.A).left (snd (TFK (R := V) F) A.A).left (TFK (R := V) F).hom A.A.hom :=
    IsPullback.of_hasPullback _ _
  have key : ∀ (v : epsR (FractionRing V) ⟶ A.A) yA,
      IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v →
      VecAt U.toUnifPre F y yA →
      yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
    intro v yA hv hy
    refine hφ.hom_ext ?_ ?_
    · rw [Category.assoc, hy.2, Category.assoc]
      unfold IsVecOver at hv
      rw [hv, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMapR]
    · rw [Category.assoc, Over.w (snd _ _), ← Over.w (fst _ _), ← Category.assoc, hy.1, Category.assoc, Over.w v]
      show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
      rw [spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap]
  obtain ⟨v, hv, hvu⟩ := existsUnique_isVecOver hφ y
  refine ⟨?_, ⟨v, hv, hvu⟩, key⟩
  have w : (spMap (algebraMap F (DualNumber F)) ≫ (TFK (R := V) F).hom) =
      (spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left) ≫ A.A.hom := by
    rw [Category.assoc, Over.w v]
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap]
  have hy : VecAt U.toUnifPre F y (hT.lift _ _ w) := by
    refine ⟨hT.lift_fst _ _ w, ?_⟩
    rw [← Category.assoc, hT.lift_snd _ _ w, Category.assoc]
    unfold IsVecOver at hv
    rw [hv, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMapR]
  refine ⟨hT.lift _ _ w, hy, fun yA h => ?_⟩
  exact hT.hom_ext ((h.1).trans (hT.lift_fst _ _ w).symm) ((key v yA hv h).trans (hT.lift_snd _ _ w).symm)

end GlobalTheory.MBLow
end
end

