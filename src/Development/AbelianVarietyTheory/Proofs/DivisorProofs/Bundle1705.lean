import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyCechVanishingAboveDegree
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem not_NV_of_ge :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
      ∃ c : ℕ, ∀ P : LB A.left, P.IsLB → ∀ j : ℕ, c ≤ j → ¬ NV A P j := by
  intro K _ _ A _ hA
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hsep : IsSeparated A.hom := inferInstance
  obtain ⟨m, V, hV, hc⟩ :=
    GlobalTheory.exists_fin_affine_cover (X := A.left) (V := ⊤) (by simpa using isCompact_univ)
  refine ⟨m, fun P hP j hj hNV => ?_⟩
  obtain ⟨κ, _, _, W, hW, hWc, hne⟩ := hNV
  obtain ⟨e⟩ := GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers K A.left A.hom P κ W (Fin m) V
    hP hsep hW hWc hV hc j
  apply hne
  have hz : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).X j) :=
    GlobalTheory.AbLaw.isZero_cechLB_X A.hom P V (by simpa using hj)
  have h0 : IsZero ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (HomologicalComplex.ExactAt.of_isZero hz)
  have : Subsingleton ((GlobalTheory.AbLaw.cechLB A.hom P V).homology j) :=
    ModuleCat.isZero_iff_subsingleton.1 h0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton)

end GlobalTheory.AmpleGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByChartsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_isProjectiveOverRingByCharts : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom := by
  first | exact @GlobalTheory.ProjField.isProjBy_of_isAbelianScheme | exact GlobalTheory.ProjField.isProjBy_of_isAbelianScheme | (intros; apply GlobalTheory.ProjField.isProjBy_of_isAbelianScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqUnderOfIdemAt
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.NormLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem absNorm_eq_under_of_idemAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm (P.asIdeal.under (𝓞 D.host.F)) := by
  classical
  have hns := Formalism.IndefR.Fin.idemAt_split he
  let c : 𝓞 D.host.E ≃+* 𝓞 D.host.E := Formalism.DivisionValues.cO D.host.E
  have hc : ∀ x : 𝓞 D.host.E, ((c x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := fun x => rfl
  have hcc : ∀ x, c (c x) = x := fun x => RingOfIntegers.ext (by rw [hc, hc, star_star])
  have hcF : ∀ a : 𝓞 D.host.F, c (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a :=
    fun a => RingOfIntegers.ext (by
      rw [hc]
      exact Formalism.IndefR.Eqv.star_algebraMapF D (a : D.host.F))
  let Q : Ideal (𝓞 D.host.E) := P.asIdeal.comap (c : 𝓞 D.host.E →+* 𝓞 D.host.E)
  have hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQv : Q.under (𝓞 D.host.F) = P.asIdeal.under (𝓞 D.host.F) := by
    ext a
    show c (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ∈ P.asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P.asIdeal
    rw [hcF]
  have hne : Q ≠ P.asIdeal := by
    intro h
    apply hns
    intro x hx
    have hx' : c x ∈ Q := by
      show c (c x) ∈ P.asIdeal
      rw [hcc]; exact hx
    rw [h] at hx'
    exact ⟨c x, hx', hc x⟩
  set p := P.asIdeal.under (𝓞 D.host.F) with hp
  have hp0 : p ≠ ⊥ := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
  have hpP : p.IsPrime := Ideal.IsPrime.comap _
  have hpM : p.IsMaximal := hpP.isMaximal hp0
  haveI hl1 : P.asIdeal.LiesOver p := ⟨rfl⟩
  haveI hl2 : Q.LiesOver p := ⟨hQv.symm⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 D.host.E)
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E, D.sp.cm.deg2] at hsum
  let P1 : p.primesOver (𝓞 D.host.E) := ⟨P.asIdeal, P.isPrime, hl1⟩
  let Q1 : p.primesOver (𝓞 D.host.E) := ⟨Q, hQp, hl2⟩
  have h12 : P1 ≠ Q1 := fun h => hne (congrArg Subtype.val h).symm
  have hpos : ∀ R : p.primesOver (𝓞 D.host.E),
      1 ≤ R.1.ramificationIdx (𝓞 D.host.F) * R.1.inertiaDeg (𝓞 D.host.F) := fun R =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hle : P1.1.ramificationIdx (𝓞 D.host.F) * P1.1.inertiaDeg (𝓞 D.host.F) +
      Q1.1.ramificationIdx (𝓞 D.host.F) * Q1.1.inertiaDeg (𝓞 D.host.F) ≤ 2 := by
    rw [← hsum, ← Finset.sum_pair (f := fun R : p.primesOver (𝓞 D.host.E) =>
      R.1.ramificationIdx (𝓞 D.host.F) * R.1.inertiaDeg (𝓞 D.host.F)) h12]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h1 := hpos P1
  have h2 := hpos Q1
  have hef : P.asIdeal.ramificationIdx (𝓞 D.host.F) * P.asIdeal.inertiaDeg (𝓞 D.host.F) = 1 := by
    change P1.1.ramificationIdx (𝓞 D.host.F) * P1.1.inertiaDeg (𝓞 D.host.F) = 1
    omega
  have hf : P.asIdeal.inertiaDeg (𝓞 D.host.F) = 1 := Nat.eq_one_of_mul_eq_one_left hef
  rw [← Ideal.absNorm_pow_inertiaDeg p P.asIdeal, hf, pow_one]

variable {T : Type} {L : LevCh D T}

open Classical in

theorem absNorm_w (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    Ideal.absNorm (P.w v).asIdeal = Ideal.absNorm v.asIdeal := by
  have hv' : v ∈ insert P.v0 (S1 D) := by
    rcases P.mem_S0_of_sum_eq.1 hv with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem h
  obtain ⟨e, he⟩ := P.w_split v hv'
  have hu : (P.w v).asIdeal.under (𝓞 D.host.F) = v.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal, P.under_w hv]
  rw [absNorm_eq_under_of_idemAt he, hu]

theorem absNorm_condE : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L), Ideal.absNorm (GlobalTheory.FunObj.SqNum.condE P) = GlobalTheory.FunObj.SqNum.levQ P := by
  intro D T L P
  unfold GlobalTheory.FunObj.SqNum.condE GlobalTheory.FunObj.SqNum.levQ
  rw [map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [map_pow, absNorm_w P hv]

end GlobalTheory.FunObj.NormLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMinpolyCoeffZeroPowNumberFieldStatement
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_norm_minpoly_coeff_zero_pow_numberField : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → IsAlgebraic ℚ β → |(Algebra.norm ℚ (p.coeff 0) : ℚ)| ^ (minpoly ℚ β).natDegree = |(minpoly ℚ β).coeff 0| ^ (p.natDegree * Module.finrank ℚ K) := by
  first | exact @GlobalTheory.NormTower.abs_norm_coeff_zero_pow | exact GlobalTheory.NormTower.abs_norm_coeff_zero_pow | (intros; apply GlobalTheory.NormTower.abs_norm_coeff_zero_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMulMemHatId
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.BlockIdx

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))

theorem gen_mem_hatId {b : 𝓞 D.host.E} (hb : b ∈ 𝔪) {s : AE D} (hs : s ∈ OhE D) :
    inc D (b : D.host.E) * s ∈ hatId D 𝔪 :=
  AddSubgroup.subset_closure ⟨b, hb, s, hs, rfl⟩

theorem mul_mem_hatId {s : AE D} (hs : s ∈ OhE D) {x : AE D} (hx : x ∈ hatId D 𝔪) :
    s * x ∈ hatId D 𝔪 := by
  have h : AddSubgroup.closure {y | ∃ b ∈ 𝔪, ∃ t ∈ OhE D, y = inc D (b : D.host.E) * t} ≤
      (hatId D 𝔪).comap (AddMonoidHom.mulLeft s) := by
    rw [AddSubgroup.closure_le]
    rintro y ⟨b, hb, t, ht, rfl⟩
    show s * (inc D (b : D.host.E) * t) ∈ hatId D 𝔪
    rw [mul_left_comm]
    exact gen_mem_hatId D 𝔪 hb (mul_mem hs ht)
  exact h hx

theorem absNorm_mul_mem_hatId {w : AE D} (hw : w ∈ OhE D) :
    (Ideal.absNorm 𝔪 : AE D) * w ∈ hatId D 𝔪 := by
  have := gen_mem_hatId D 𝔪 (Ideal.absNorm_mem 𝔪) hw
  simpa using this

theorem exists_red (h𝔪 : 𝔪 ≠ ⊥) (x : AE D) (hx : x ∈ OhE D) :
    ∃ r : 𝓞 D.host.E, x - inc D (r : D.host.E) ∈ hatId D 𝔪 := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  obtain ⟨r, hr, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D _ hn x hx
  refine ⟨⟨r, (mem_integralClosure_iff ℤ _).2 hr⟩, ?_⟩
  show x - inc D r ∈ hatId D 𝔪
  rw [e, add_sub_cancel_left]
  exact absNorm_mul_mem_hatId D 𝔪 hw

theorem mem_blockJ_of_congr {a N : ℕ} {k₁ k₂ : GA D N} (h₁ : k₁ ∈ intG D N) (h₂ : k₂ ∈ intG D N)
    (h : ∀ i j, ((k₂ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
      ((k₁ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪) :
    k₁⁻¹ * k₂ ∈ blockJ D 𝔪 a N := by
  apply Subgroup.subset_closure
  refine ⟨(intG D N).mul_mem ((intG D N).inv_mem h₁) h₂, fun i j hj hi => ?_⟩
  have hij : i ≠ j := fun e => by subst e; omega
  have hinv := (mem_intG k₁).1 h₁
  have e : (((k₁⁻¹ * k₂ : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      (((k₁ : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        (((k₂ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) -
          ((k₁ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) + 1 := by
    rw [Matrix.mul_sub, Units.inv_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    abel
  rw [e, Matrix.add_apply, Matrix.one_apply_ne hij, add_zero, Matrix.mul_apply]
  exact AddSubgroup.sum_mem _ fun l _ => mul_mem_hatId D 𝔪 ((hinv i l).2) (h l j)

end GlobalTheory.BotPairSmall.BlockIdx

namespace GlobalTheory.BotPairSmall

open BlockIdx in

theorem blockJ_relIndex : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (a N : ℕ),
    (GlobalTheory.BotPairSmall.blockJ D 𝔪 a N).relIndex (intG D N) ≠ 0 ∧
      (GlobalTheory.BotPairSmall.blockJ D 𝔪 a N).relIndex (intG D N) ≤ Ideal.absNorm 𝔪 ^ (N ^ 2) := by
  intro D 𝔪 h𝔪 a N
  have hent : ∀ k : intG D N, ∀ i j,
      (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D :=
    fun k i j => (((mem_intG _).1 k.2) i j).1
  choose r hr using fun (k : intG D N) i j => exists_red D 𝔪 h𝔪 _ (hent k i j)
  let H := (blockJ D 𝔪 a N).subgroupOf (intG D N)
  let f : (intG D N ⧸ H) → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) :=
    fun q i j => Ideal.Quotient.mk 𝔪 (r q.out i j)
  have hf : Function.Injective f := by
    intro q₁ q₂ e
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv]
    refine mem_blockJ_of_congr D 𝔪 q₁.out.2 q₂.out.2 fun i j => ?_
    have e' : Ideal.Quotient.mk 𝔪 (r q₁.out i j) = Ideal.Quotient.mk 𝔪 (r q₂.out i j) :=
      congrFun (congrFun e i) j
    rw [Ideal.Quotient.eq] at e'
    have := sub_mem (sub_mem (hr q₂.out i j) (gen_mem_hatId D 𝔪 e' (one_mem (OhE D)))) (hr q₁.out i j)
    convert this using 1
    push_cast
    rw [map_sub]
    ring
  have hcard : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  haveI : Finite (intG D N ⧸ H) := Finite.of_injective f hf
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  show H.index ≤ _
  rw [Subgroup.index]
  calc Nat.card (intG D N ⧸ H) ≤ Nat.card (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) := Nat.card_le_card_of_injective f hf
    _ = Ideal.absNorm 𝔪 ^ (N ^ 2) := by
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, hcard, ← pow_mul, sq]

end GlobalTheory.BotPairSmall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsOriginBoxValueExponentLe
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem abs_lin_le (a a' u w M : ℤ) (hu : |u| ≤ M) (hw : |w| ≤ M) : |a * u - a' * w| ≤ M * (|a| + |a'|) := by
  calc |a * u - a' * w| ≤ |a * u| + |a' * w| := abs_sub _ _
    _ = |a| * |u| + |a'| * |w| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * M + |a'| * M := add_le_add (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hw (abs_nonneg _))
    _ = M * (|a| + |a'|) := by ring

theorem abs_list_sum_le {α : Type*} (f : α → ℤ) (C : ℤ) :
    ∀ l : List α, (∀ b ∈ l, |f b| ≤ C) → |(l.map f).sum| ≤ l.length * C
  | [], _ => by simp
  | b :: l, h => by
    have h1 := h b (by simp)
    have h2 := abs_list_sum_le f C l fun x hx => h x (by simp [hx])
    rw [List.map_cons, List.sum_cons, List.length_cons]
    calc |f b + (l.map f).sum| ≤ |f b| + |(l.map f).sum| := abs_add_le _ _
      _ ≤ C + l.length * C := add_le_add h1 h2
      _ = ((l.length + 1 : ℕ) : ℤ) * C := by push_cast; ring

theorem abs_auxiliaryVectorUniformizerExponent_le (a a' : ℤ) {n : Type*} (c M : ℕ) (hc : c ≤ M) (y : n ⊕ Fin c) :
    |auxiliaryVectorUniformizerExponent a a' c y| ≤ (M : ℤ) * (|a| + |a'|) := by
  rcases y with x | p
  · simp only [auxiliaryVectorUniformizerExponent, abs_zero]; positivity
  · simp only [auxiliaryVectorUniformizerExponent]
    have hp := p.2
    apply abs_lin_le
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem abs_vtxExp_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (j x : ℕ) (hx : x < G.rank (G.m, j)) :
    |vtxExp a a' (G.m - 1 - j) (topRank G j) x| ≤ (G.m : ℤ) * (|a| + |a'|) := by
  have key := topRank_add hs j
  unfold vtxExp
  split_ifs with h
  · apply abs_lin_le
    · rw [abs_of_nonneg (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega
  · simp only [abs_zero]; positivity

theorem abs_vtxDet_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) (X : ℕ × ℕ) (hX : X.2 ≤ G.m) :
    |vtxDet G a a' X| ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by
  unfold vtxDet
  split_ifs with h
  · calc |∑ x : Fin (G.rank (G.m, X.2)), vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x|
          ≤ ∑ x : Fin (G.rank (G.m, X.2)), |vtxExp a a' (G.m - 1 - X.2) (topRank G X.2) x| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : Fin (G.rank (G.m, X.2)), (G.m : ℤ) * (|a| + |a'|) :=
            Finset.sum_le_sum fun x _ => abs_vtxExp_le G hs a a' X.2 x x.2
      _ = (G.rank (G.m, X.2) : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by simp
      _ ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hN _ _ le_rfl hX
  · simp only [abs_zero]; positivity

theorem mem_oppositePath_bound {m : ℕ} {b : Edge} (hb : b ∈ oppositePath m) :
    b.src.1 ≤ m ∧ b.src.2 ≤ m ∧ b.tgt.1 ≤ m ∧ b.tgt.2 ≤ m := by
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · simp only [Edge.src, Edge.tgt]; omega
  · simp only [Edge.src, Edge.tgt]; omega

theorem length_oppositePath (m : ℕ) : (oppositePath m).length = 2 * m := by
  simp [oppositePath]; ring

theorem abs_pathSum_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) :
    |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
      ≤ ((2 * G.m : ℕ) : ℤ) * (2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))))) := by
  rw [← length_oppositePath]
  apply abs_list_sum_le
  intro b hb
  obtain ⟨h1, h2, h3, h4⟩ := mem_oppositePath_bound hb
  have e1 := abs_vtxDet_le G hs a a' N hN b.src h2
  have e2 := abs_vtxDet_le G hs a a' N hN b.tgt h4
  have r1 : ((G.rank b.tgt : ℕ) : ℤ) ≤ N := by exact_mod_cast hN _ _ h3 h4
  have r2 : ((G.rank b.src : ℕ) : ℤ) ≤ N := by exact_mod_cast hN _ _ h1 h2
  have hC : 0 ≤ (N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)) := by positivity
  calc |vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src|
        ≤ |vtxDet G a a' b.src * G.rank b.tgt| + |vtxDet G a a' b.tgt * G.rank b.src| := abs_sub _ _
    _ = |vtxDet G a a' b.src| * G.rank b.tgt + |vtxDet G a a' b.tgt| * G.rank b.src := by
        rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
    _ ≤ ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))) * N + ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))) * N :=
        add_le_add (mul_le_mul e1 r1 (by positivity) hC) (mul_le_mul e2 r2 (by positivity) hC)
    _ = 2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|)))) := by ring

theorem abs_boxExp_le (G : Grid k) (a a' : ℤ) (j : Fin (G.m - 1))
    (v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) :
    |boxExp G a a' j v| ≤ (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by
  have hj := j.2
  have e1 := abs_auxiliaryVectorUniformizerExponent_le a a' (G.m - 2 - j + 1) G.m (by omega) v.1.2
  have e2 := abs_auxiliaryVectorUniformizerExponent_le a a' (G.m - 2 - j) G.m (by omega) v.1.1
  unfold boxExp
  have ha : |a| ≤ |a| + |a'| := le_add_of_nonneg_right (abs_nonneg _)
  calc |a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2 + auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1|
        ≤ |a - auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1| := abs_add_le _ _
    _ ≤ |a| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) v.1.2| + |auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) v.1.1| := by
        gcongr; exact abs_sub _ _
    _ ≤ (|a| + |a'|) + (G.m : ℤ) * (|a| + |a'|) + (G.m : ℤ) * (|a| + |a'|) := by gcongr
    _ = (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by ring

open Classical in
theorem card_stepVar_le (G : Grid k) (hs : 1 ≤ G.s) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) (j : Fin (G.m - 1)) :
    Fintype.card (StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) ≤ N * N := by
  have hj := j.2
  have k0 := topRank_add hs j
  have k1 := topRank_add hs ((j : ℕ) + 1)
  have n0 := hN G.m j le_rfl (by omega)
  have n1 := hN G.m (j + 1) le_rfl (by omega)
  refine (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans ?_
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  exact Nat.mul_le_mul (by omega) (by omega)

open Classical in
theorem abs_boxSum_le (G : Grid k) (hs : 1 ≤ G.s) (a a' : ℤ) (N : ℕ)
    (hN : ∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) :
    |∑ j, ∑ v, boxExp G a a' j v| ≤ ((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|))) := by
  have hC : 0 ≤ (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := by positivity
  calc |∑ j, ∑ v, boxExp G a a' j v| ≤ ∑ j, |∑ v, boxExp G a a' j v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (G.m - 1), (N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc |∑ v, boxExp G a a' j v| ≤ ∑ v, |boxExp G a a' j v| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _v : StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j)),
                (2 * (G.m : ℤ) + 1) * (|a| + |a'|) := Finset.sum_le_sum fun v _ => abs_boxExp_le G a a' j v
          _ = (Fintype.card (StepVar (Fin (topRank G ((j : ℕ) + 1))) (G.m - 2 - j) (Fin (topRank G j))) : ℤ) *
                ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by simp
          _ ≤ (N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)) := by
                apply mul_le_mul_of_nonneg_right _ hC
                exact_mod_cast card_stepVar_le G hs N hN j
    _ = ((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|))) := by simp

theorem abs_expo_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (G : Grid k), 1 ≤ G.s → ∀ (a a' : ℤ) (N : ℕ), (∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) →
      |expo G a a'| ≤ 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by
  intro k _ _ _ _ G hs a a' N hN
  classical
  have hP := abs_pathSum_le G hs a a' N hN
  have hB := abs_boxSum_le G hs a a' N hN
  have hpoly : 4 * (G.m : ℤ) ^ 2 + 2 * ((G.m - 1 : ℕ) : ℤ) * (2 * (G.m : ℤ) + 1) ≤ 8 * (G.m : ℤ) ^ 3 := by
    rcases Nat.eq_zero_or_pos G.m with h | h
    · simp [h]
    · have h1 : ((G.m - 1 : ℕ) : ℤ) = (G.m : ℤ) - 1 := by push_cast [Nat.cast_sub h]; ring
      have h2 : (1 : ℤ) ≤ G.m := by exact_mod_cast h
      rw [h1]; nlinarith
  have hT : 0 ≤ (N : ℤ) ^ 2 * (|a| + |a'|) := by positivity
  unfold expo
  calc _ ≤ |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
          + |2 * ∑ j, ∑ v, boxExp G a a' j v| := abs_sub _ _
    _ = |((oppositePath G.m).map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum|
          + 2 * |∑ j, ∑ v, boxExp G a a' j v| := by rw [abs_mul]; norm_num
    _ ≤ ((2 * G.m : ℕ) : ℤ) * (2 * ((N : ℤ) * ((N : ℤ) * ((G.m : ℤ) * (|a| + |a'|))))) +
          2 * (((G.m - 1 : ℕ) : ℤ) * ((N : ℤ) * N * ((2 * (G.m : ℤ) + 1) * (|a| + |a'|)))) := by gcongr
    _ = (4 * (G.m : ℤ) ^ 2 + 2 * ((G.m - 1 : ℕ) : ℤ) * (2 * (G.m : ℤ) + 1)) * ((N : ℤ) ^ 2 * (|a| + |a'|)) := by
          push_cast; ring
    _ ≤ 8 * (G.m : ℤ) ^ 3 * ((N : ℤ) ^ 2 * (|a| + |a'|)) := mul_le_mul_of_nonneg_right hpoly hT
    _ = 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by ring

end GlobalTheory.OriginBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.SchrLoc

open GlobalTheory.VacAny

theorem eq_atPlace_of_at {F : Type} [Field F] [NumberField F] {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {z : AF F}
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z) :
    z = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v z) := by
  have h1 := hz (1 - GlobalTheory.EmbChart.atPlace v 1)
    (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  conv_lhs => rw [h1]
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

theorem schr_tens_of_at : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 i)) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 i)) → ∀ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    (∀ x z : κ → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → r (x + z) = r x) →
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) φ r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
        (GlobalTheory.WeilM.schr (GlobalTheory.VacAny.psiV ψ v) (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i), fun i => GlobalTheory.AdelicU.evFin F v (w.2 i)) φ) r := by
  intro F _ _ ψ v κ _ w h1 h2 φ r hr
  funext x
  have hr' : r (x + w.1) = r x := hr x w.1 (at_pi h1)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
    at_add (at_sum _ fun i _ => at_mul_left _ (h2 i))
      (at_mul_left _ (at_sum _ fun i _ => at_mul_left _ (h2 i)))
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
  rw [hr', eq_atPlace_of_at hz, ← psiV_apply]
  simp only [dotProduct, map_add, map_mul, map_sum, evFin_invOf_two, Pi.add_apply]
  rw [show (fun i => GlobalTheory.AdelicU.evFin F v (x i) + GlobalTheory.AdelicU.evFin F v (w.1 i)) =
    (fun i => GlobalTheory.AdelicU.evFin F v (x i)) + (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i)) from rfl]
  ring

end GlobalTheory.SchrLoc
end

