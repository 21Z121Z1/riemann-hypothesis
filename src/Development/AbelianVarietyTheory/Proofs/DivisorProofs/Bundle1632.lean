import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCardKilledByIdealEqAbsNormPow
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HTTorsCount

theorem absNorm_pos_coprime {K : Type} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
    (𝔟 : Ideal (𝓞 K)) (h : 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} = ⊤) :
    0 < Ideal.absNorm 𝔟 ∧ (Ideal.absNorm 𝔟).Coprime p := by
  obtain ⟨β, hβ, z, hz, hsum⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top (x := (1 : 𝓞 K)))
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hpos : 0 < Ideal.absNorm 𝔟 := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    rintro rfl
    rw [Submodule.mem_bot] at hβ
    subst hβ
    rw [zero_add, _root_.mul_comm] at hsum
    have hu : IsUnit (p : 𝓞 K) := isUnit_iff_exists_inv.2 ⟨y, hsum⟩
    have e : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 K))
    rw [e, Algebra.norm_algebraMap, Int.isUnit_iff_natAbs_eq, Int.natAbs_pow, Int.natAbs_natCast] at hn
    rcases Nat.pow_eq_one.1 hn with h1 | h1
    · exact hp.out.one_lt.ne' h1
    · exact (Module.finrank_pos (R := ℤ) (M := 𝓞 K)).ne' h1
  refine ⟨hpos, ?_⟩
  refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hd => ?_))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd hpos
  have : Finite (𝓞 K ⧸ 𝔟) := Nat.finite_of_card_ne_zero hpos.ne'
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hd
  have hpx : (p : 𝓞 K ⧸ 𝔟) * x = 0 := by rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have h1 : Ideal.Quotient.mk 𝔟 y * (p : 𝓞 K ⧸ 𝔟) = 1 := by
    have := congrArg (Ideal.Quotient.mk 𝔟) hsum
    rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hβ, zero_add, map_mul, map_natCast, map_one] at this
  have hx0 : x = 0 := by
    calc x = (Ideal.Quotient.mk 𝔟 y * (p : 𝓞 K ⧸ 𝔟)) * x := by rw [h1, _root_.one_mul]
      _ = 0 := by rw [_root_.mul_assoc, hpx, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  exact hp.out.one_lt.ne hx

theorem card_killedBy_eq_absNorm_pow : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} = Ideal.absNorm 𝔟 ^ (D.m * D.n) := by
  intro p _ D R _ b N S s o 𝔟 h𝔟 k _ _ t
  obtain ⟨hcpos, hcop⟩ := absNorm_pos_coprime p 𝔟 h𝔟
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, spMap β = t ≫ s := ⟨(Spec.preimage (t ≫ s)).hom, Spec.map_preimage _⟩
  obtain ⟨I, -⟩ := o.geom k t β hβ.symm
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have hsmul : ∀ (a : 𝓞 D.F) (x : D.La), a • x = (algebraMap (𝓞 D.F) D.O a) • x := fun _ _ => rfl
  have hcnt := GlobalTheory.T.card_killed_by_ideal_mod_int_eq_absNorm_pow D.F D.La D.freeLa D.finLa (D.m * D.n) D.rankLa 𝔟 (Ideal.absNorm 𝔟) hcpos
    (Ideal.absNorm_mem 𝔟)
  rw [← hcnt]
  set c := Ideal.absNorm 𝔟 with hc
  set P : Submodule (𝓞 D.F) D.La := Ideal.span {(c : 𝓞 D.F)} • (⊤ : Submodule (𝓞 D.F) D.La) with hP
  have hmemP : ∀ x, x ∈ P ↔ ∃ y, x = c • y := by
    intro x
    rw [hP, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, by rw [hsmul, map_natCast, Nat.cast_smul_eq_nsmul]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, Submodule.mem_top, by rw [hsmul, map_natCast, Nat.cast_smul_eq_nsmul]⟩
  let g : D.La → (Over.mk t ⟶ o.A) := I.ev c
  have hker : ∀ x, g x = 1 ↔ x ∈ P := fun x => by rw [hmemP]; exact I.ker c hcpos hcop x
  have hsub : ∀ x y, g (x - y) = g x * (g y)⁻¹ := fun x y =>
    eq_mul_inv_of_mul_eq (by rw [← I.add, sub_add_cancel])
  have hlin : ∀ (a : 𝓞 D.F) x, g (a • x) = g x ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := fun a x => by
    rw [hsmul]; exact I.lin c _ x
  have hmap : 𝔟.map (algebraMap (𝓞 D.F) D.O) = Ideal.span (algebraMap (𝓞 D.F) D.O '' 𝔟) := rfl
  let f : D.La ⧸ P → (Over.mk t ⟶ o.A) := fun z => Quotient.liftOn' z g (fun x y hxy => by
    have h1 : g (x - y) = 1 := (hker _).2 ((Submodule.quotientRel_def P).1 hxy)
    rw [hsub] at h1
    exact mul_inv_eq_one.1 h1)
  have hf : ∀ x, f (Submodule.Quotient.mk x) = g x := fun _ => rfl
  have hkill : ∀ x, (∀ a ∈ 𝔟, a • (Submodule.Quotient.mk x : D.La ⧸ P) = 0) ↔
      GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) (g x) := by
    intro x
    rw [hmap, GlobalTheory.IwLevel.killedBy_span]
    constructor
    · rintro h _ ⟨a, ha, rfl⟩
      rw [GlobalTheory.IwLevel.htAct_act, ← hlin, hker, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact h a ha
    · intro h a ha
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← hker, hlin]
      have := h _ ⟨a, ha, rfl⟩
      rwa [GlobalTheory.IwLevel.htAct_act] at this
  have hpow : ∀ (q : Over.mk t ⟶ o.A) (n : ℕ), q ≫ o.act.act (n : D.O) = q ^ n := by
    intro q n
    have h0 : o.act.act 0 = 1 := by
      have := o.act.add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    induction n with
    | zero => rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, o.act.add, o.act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]
  let F : {z : D.La ⧸ P // ∀ a ∈ 𝔟, a • z = 0} →
      {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} :=
    fun z => ⟨f z.1, by
      obtain ⟨z, hz⟩ := z
      induction z using Submodule.Quotient.induction_on with
      | H x => exact (hkill x).1 hz⟩
  refine (Nat.card_eq_of_bijective F ⟨?_, ?_⟩).symm
  · rintro ⟨z₁, h₁⟩ ⟨z₂, h₂⟩ h
    have h' : f z₁ = f z₂ := congrArg Subtype.val h
    induction z₁ using Submodule.Quotient.induction_on with
    | H x =>
    induction z₂ using Submodule.Quotient.induction_on with
    | H y =>
    rw [hf, hf] at h'
    apply Subtype.ext
    change Submodule.Quotient.mk x = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq, ← hker, hsub, h', mul_inv_cancel]
  · rintro ⟨q, hq⟩
    have hq1 : q ^ c = 1 := by
      rw [← hpow, ← map_natCast (algebraMap (𝓞 D.F) D.O)]
      have := hq _ (Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) (Ideal.absNorm_mem 𝔟))
      rwa [GlobalTheory.IwLevel.htAct_act] at this
    obtain ⟨x, hx⟩ := (I.onto c hcpos hcop q).1 hq1
    refine ⟨⟨Submodule.Quotient.mk x, (hkill x).2 (by change GlobalTheory.IwLevel.KilledBy _ _ (I.ev c x); rw [hx]; exact hq)⟩, Subtype.ext ?_⟩
    exact hx

end GlobalTheory.HTTorsCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackCompFactors
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.PullFactor

theorem objMap_factor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₀ S₁ T : Scheme.{0}) (s₀ : S₀ ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (t : T ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o : GlobalTheory.UPel.HT.Obj b N t) (g : S₁ ⟶ S₀) (h : T ⟶ S₁), GlobalTheory.UPel.HT.ObjMap o₁ o₀ g → GlobalTheory.UPel.HT.ObjMap o o₀ (h ≫ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o o₁ h) := by
  intro p _ D R _ b N S₀ S₁ T s₀ s₁ t o₀ o₁ o g h m₁ m
  exact GlobalTheory.UPel.HT.MapComp.cancel m m₁

end GlobalTheory.UPel.HT.PullFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTDim

theorem card_torsion_of_ev {La Q : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] [Group Q]
    (ev : La → Q) (ℓ : ℕ) (hℓ : 0 < ℓ) (hadd : ∀ x y, ev (x + y) = ev x * ev y)
    (hker : ∀ x, ev x = 1 ↔ ∃ y, x = ℓ • y) (honto : ∀ q, q ^ ℓ = 1 ↔ ∃ x, ev x = q) :
    Nat.card {q : Q // q ^ ℓ = 1} = ℓ ^ Module.finrank ℤ La := by
  haveI : NeZero ℓ := ⟨by omega⟩
  let f : La →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (ev x)) fun x y => by
    rw [hadd]; rfl
  let r := Module.finrank ℤ La
  let b := Module.finBasis ℤ La
  let g : La →+ (Fin r → ZMod ℓ) := AddMonoidHom.mk' (fun x i => ((b.repr x i : ℤ) : ZMod ℓ)) fun x y => by
    ext i; simp
  have hg : Function.Surjective g := by
    intro v
    choose w hw using fun i => ZMod.intCast_surjective (v i)
    refine ⟨b.equivFun.symm w, funext fun i => ?_⟩
    show ((b.repr (b.equivFun.symm w) i : ℤ) : ZMod ℓ) = v i
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hw]
  have hk : f.ker = g.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
    change Additive.ofMul (ev x) = 0 ↔ _
    rw [ofMul_eq_zero, hker]
    constructor
    · rintro ⟨y, rfl⟩
      ext i
      simp [g]
    · intro h
      have hd : ∀ i, (ℓ : ℤ) ∣ b.repr x i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact congrFun h i
      choose c hc using hd
      refine ⟨b.equivFun.symm c, b.ext_elem fun i => ?_⟩
      have hcy : b.repr (b.equivFun.symm c) i = c i := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      rw [map_nsmul, Finsupp.smul_apply, hcy, hc i, nsmul_eq_mul]
  have e1 : Nat.card {q : Q // q ^ ℓ = 1} = Nat.card f.range := by
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun q => ?_)
    rw [honto, AddMonoidHom.mem_range]
    rfl
  rw [e1, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hk).toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv]
  simp [Nat.card_eq_fintype_card, r]

variable {p : ℕ} [Fact p.Prime]

theorem relDim {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b N s) : SmoothOfRelativeDimension D.g o.A.hom := by
  have := o.ab.smooth
  choose n W hW hd using H1.exists_dim o.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D.g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension D.g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := AlgebraicClosure (o.A.left.residueField y)
  let z : Sp k ⟶ o.A.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (o.A.left.residueField y) k)) ≫ o.A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ o.A.hom
  let β : R →+* k := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  let B := (Over.pullback x).obj o.A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj x o.A o.ab
  obtain ⟨m, hm⟩ := GlobalTheory.AbVarRelDim.exists_relDim k B hB
  let z' : Sp k ⟶ pullback o.A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst o.A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ o.A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hℓp : (p + 1).Coprime p := Nat.coprime_self_add_left.2 (Nat.coprime_one_left p)
  have hℓk : ((p + 1 : ℕ) : k) ≠ 0 := by
    intro h0
    have := (b.unit (p + 1) hℓp).map β
    rw [map_natCast, h0] at this
    exact not_isUnit_zero this
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨I, -⟩ := o.geom k x β hβ
  have c1 := card_torsion_of_ev (I.ev (p + 1)) (p + 1) (by omega) (I.add (p + 1)) (I.ker (p + 1) (by omega) hℓp)
    (I.onto (p + 1) (by omega) hℓp)
  have c2 := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B m (p + 1) hB hm hℓk
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback o.A x) (𝟙 (Sp k)) x
    (Category.id_comp x).symm
  have c3 : Nat.card {q : 𝟙_ (Over (Sp k)) ⟶ B // q ^ (p + 1) = 1} =
      Nat.card {q : Over.mk x ⟶ o.A // q ^ (p + 1) = 1} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun q => by
      change q ^ (p + 1) = 1 ↔ e q ^ (p + 1) = 1
      rw [← map_pow, map_eq_one_iff e e.injective])
  have hr := D.rankLa
  have h2 : 2 * m = Module.finrank ℤ D.La :=
    Nat.pow_right_injective (by have := (Fact.out : p.Prime).two_le; omega : 2 ≤ p + 1) (by
      show (p + 1) ^ (2 * m) = (p + 1) ^ Module.finrank ℤ D.La
      rw [← c2, c3, c1])
  have hg : D.g = m := by
    show D.m * D.n * Module.finrank ℚ D.F / 2 = m
    omega
  rw [hg, ← e₁]
  exact hd y

theorem relDim_and_isLB : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), SmoothOfRelativeDimension D.g o.A.hom ∧ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB :=
  fun _ _ _ _ _ _ _ _ _ o => ⟨relDim o, LB.isLB_pull o.isLB _⟩

end GlobalTheory.HTDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhaseStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOp_realLine_add_eq_phase_mul_shifted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ) (w : Formalism.IndefR.DatumF.WOF F E nS nT) (s t : ℝ),
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L (s + t)) f w = B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L s)) * Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L s) := by
  first | exact @GlobalTheory.heisOF_line_add | exact GlobalTheory.heisOF_line_add | (intros; apply GlobalTheory.heisOF_line_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFixedInvariantOpenCompactCompactSupporStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_fixed_invariant_open_compact_compact_support : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))) →
      ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧ IsCompact K ∧
        ∀ Φ : (κ → AF D.host.F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 D.host.F m) Φ = Φ) →
          (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE D.host.F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 := by
  first | exact @GlobalTheory.WeilAdm.fixed_invariant_compactSupport | exact GlobalTheory.WeilAdm.fixed_invariant_compactSupport | (intros; apply GlobalTheory.WeilAdm.fixed_invariant_compactSupport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingFixedFieldInertiaStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselianLocalRing_fixedField_inertia_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → HenselianLocalRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  first | exact @GlobalTheory.henselianLocalRing_fixedField_inertia | exact GlobalTheory.henselianLocalRing_fixedField_inertia | (intros; apply GlobalTheory.henselianLocalRing_fixedField_inertia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteLocallyFreeRepresentablePrope
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem main : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro S Z z hfin hflat hlfp r
  refine GlobalTheory.T.isHilbertSchemeRepresentable_of_open_cover S Z z hfin hflat hlfp r fun s => ?_
  obtain ⟨W, A, B, _, _, _, _, _, eW, eZ, hs, hc⟩ := GlobalTheory.T.exists_local_spec_finite_free_of_finite_flat S Z z hfin hflat hlfp s
  refine ⟨W, hs, GlobalTheory.T.isHilbertSchemeRepresentable_of_iso (z ∣_ W) (Spec.map (CommRingCat.ofHom (algebraMap A B))) eW.symm eZ.symm ?_ r
    (GlobalTheory.T.hilbert_scheme_finite_free_algebra_affine_exists A B r)⟩
  rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end GlobalTheory.HilbertSch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSumStatement
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_del_finset_sum : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld), (∀ j, A.IsForm (α j)) → A.del (∑ j, α j) = ∑ j, A.del (α j) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_finset_sum | exact GlobalTheory.CxForm.HolAtlas.del_finset_sum | (intros; apply GlobalTheory.CxForm.HolAtlas.del_finset_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementFirst
section
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.LeviPlaneHom

open Matrix GlobalTheory.LeviElem GlobalTheory.LeviHom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_flip_skew (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (skew : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → E) : form σ J v w = -σ (form σ J w v) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [skew]
  ring

def skew2 : Matrix (Fin 2) (Fin 2) E := !![0, 1; -1, 0]

theorem gram_block_skew (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {b : ℕ} (W : Spc F E (b + 2)) (W₁ : Spc F E b)
    (H : Plane E (b + 2) b) (skew : ∀ i j, σ (W.J j i) = -W.J i j)
    (hxx : form σ W.J H.x H.x = 0) (hyy : form σ W.J H.y H.y = 0) (hxy : form σ W.J H.x H.y = 1)
    (horth : ∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) (hgram : H.ιᵀ * W.J * H.ι.map σ = W₁.J) :
    (fromCols H.ι (cols2 H.x H.y))ᵀ * W.J * (fromCols H.ι (cols2 H.x H.y)).map σ = fromBlocks W₁.J 0 0 skew2 := by
  have hmap : (fromCols H.ι (cols2 H.x H.y)).map σ = fromCols (H.ι.map σ) ((cols2 H.x H.y).map σ) := by
    ext i (j | j) <;> rfl
  have ho : ∀ j, (fun i => H.ι i j) = H.ι *ᵥ Pi.single j 1 := fun j => by rw [mulVec_single_one]; rfl
  have orth' : ∀ j, form σ W.J (fun i => H.ι i j) H.x = 0 ∧ form σ W.J (fun i => H.ι i j) H.y = 0 := fun j => by
    rw [ho]; exact horth _
  rw [hmap, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols, hgram]
  congr 1
  · ext j k
    rw [form_gram, ho]
    fin_cases k
    · simpa [cols2] using (horth (Pi.single j 1)).1
    · simpa [cols2] using (horth (Pi.single j 1)).2
  · ext k j
    rw [form_gram, form_flip_skew σ hσ skew]
    fin_cases k
    · simp [cols2, (orth' j).1]
    · simp [cols2, (orth' j).2]
  · ext k k'
    rw [form_gram]
    fin_cases k <;> fin_cases k' <;>
      simp [cols2, skew2, hxx, hyy, hxy, form_flip_skew σ hσ skew H.y H.x]

theorem levi_section_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ a b, M (a * b) = M a * M b) ∧ ∀ (t : (AE F E)ˣ) (m : UA σ W.J), IsLevi (W₁ := W₁) H t 1 m → ∀ y, m * M y = M y * m := by
  intro F E _ _ _ _ _ σ _ hσ n n₁ W W₁ H hskew hn hxx hyy hxy horth hgram c₀ hc₀ hND₁ _ M hM
  subst hn
  have hdet : W₁.J.det ≠ 0 := by
    intro h0
    apply hND₁.2
    rw [det_smul, show (W₁.J.map σ).det = σ W₁.J.det from (RingHom.map_det (σ : E →+* E) _).symm, h0, map_zero, mul_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * W.J * P.map σ = fromBlocks W₁.J 0 0 skew2 :=
    gram_block_skew σ hσ W W₁ H hskew hxx hyy hxy horth hgram
  set K : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E := fromBlocks W₁.J 0 0 skew2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [skew2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * W.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * W.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  set PA := fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) with hPA
  have hPf : P.map f = PA := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * PA = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hPQ' : PA * Q.map f = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'
  have huniq : ∀ (l : (AE F E)ˣ) (g₀ : UA σ W₁.J) (h h' : UA σ W.J), IsLevi (W₁ := W₁) H l g₀ h →
      IsLevi (W₁ := W₁) H l g₀ h' → h = h' := by
    intro l g₀ h h' hL hL'
    have e : mat h = mat h' := by
      rw [← Matrix.mul_one (mat h), ← Matrix.mul_one (mat h'), ← hPQ', ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        levi_mul_cols H l g₀ h hL, levi_mul_cols H l g₀ h' hL']
    exact Subtype.ext (Units.ext e)
  refine ⟨fun a b => ?_, fun t m hm y => ?_⟩
  · have h2 := isLevi_mul H (hM a) (hM b)
    rw [mul_one] at h2
    exact huniq _ _ _ _ (hM (a * b)) h2
  · have h1 := isLevi_mul H hm (hM y)
    have h2 := isLevi_mul H (hM y) hm
    rw [mul_one, one_mul] at h1
    rw [mul_one, one_mul] at h2
    exact huniq _ _ _ _ h1 h2

end GlobalTheory.LeviPlaneHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaLimitStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_limit : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : RealT Rc P Dcf Spf Zscf S Ks), SeeEx Q → (Q.Rl.toCx3 Q.F).SEEIso Q.sEE := by
  first | exact @GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx | exact GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx | (intros; apply GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaConjMemSmulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_conj_mem_smul' : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (g σ : Ω ≃ₐ[K] Ω), σ ∈ inertia K V → g * σ * g⁻¹ ∈ inertia K (g • V) := by
  first | exact @GlobalTheory.inertia_conj_mem_smul | exact GlobalTheory.inertia_conj_mem_smul | (intros; apply GlobalTheory.inertia_conj_mem_smul <;> assumption)
end

