import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
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
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianLocalOfOrderFunction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.OrdRing

section General

variable (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]

noncomputable def intRing : ValuationSubring (FractionRing R) :=
  { (algebraMap R (FractionRing R)).range with
    mem_or_inv_mem' := fun x => by
      rcases ValuationRing.isInteger_or_isInteger R x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact Or.inl ⟨y, hy⟩
      · exact Or.inr ⟨y, hy⟩ }

noncomputable def intEquiv : R ≃+* intRing R :=
  RingEquiv.ofBijective ((algebraMap R (FractionRing R)).codRestrict (intRing R) fun y => ⟨y, rfl⟩)
    ⟨fun a b h => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h),
     fun ⟨x, ⟨y, hy⟩⟩ => ⟨y, Subtype.ext hy⟩⟩

variable {K : Type} [Field K] (φ : K →+* FractionRing R)

noncomputable def res : (intRing R).comap φ →+* R :=
  (intEquiv R).symm.toRingHom.comp (φ.restrict ((intRing R).comap φ) (intRing R) fun _ h => h)

theorem algebraMap_res (w : (intRing R).comap φ) :
    algebraMap R (FractionRing R) (res R φ w) = φ w :=
  congrArg Subtype.val ((intEquiv R).apply_symm_apply _)

theorem res_injective : Function.Injective (res R φ) := by
  intro a b h
  have := congrArg (algebraMap R (FractionRing R)) h
  rw [algebraMap_res, algebraMap_res] at this
  exact Subtype.ext (φ.injective this)

theorem dvd_of_res_dvd {x y : (intRing R).comap φ} (hy : y ≠ 0) (h : res R φ y ∣ res R φ x) :
    y ∣ x := by
  obtain ⟨c, hc⟩ := h
  have hyK : (y : K) ≠ 0 := fun h0 => hy (Subtype.ext h0)
  have hy' : algebraMap R (FractionRing R) (res R φ y) ≠ 0 := by
    rw [algebraMap_res]; exact (map_ne_zero φ).2 hyK
  have hmem : (x : K) / y ∈ (intRing R).comap φ := by
    rw [ValuationSubring.mem_comap, map_div₀, ← algebraMap_res, ← algebraMap_res, hc, map_mul,
      mul_div_cancel_left₀ _ hy']
    exact ⟨c, rfl⟩
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  show (x : K) = (y : K) * ((x : K) / y)
  field_simp

theorem isUnit_of_isUnit_res {a : (intRing R).comap φ} (h : IsUnit (res R φ a)) : IsUnit a := by
  have ha : a ≠ 0 := by rintro rfl; rw [map_zero] at h; exact not_isUnit_zero h
  refine isUnit_of_dvd_one (dvd_of_res_dvd R φ ha ?_)
  rw [map_one]; exact h.dvd

variable [IsDiscreteValuationRing R]

theorem isPrincipalIdealRing_comap : IsPrincipalIdealRing ((intRing R).comap φ) := by
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · subst hI; exact bot_isPrincipal
  obtain ⟨y0, hy0, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let s : Set ((intRing R).comap φ) := {x | x ∈ I ∧ x ≠ 0}
  have hs : s.Nonempty := ⟨y0, hy0, hne⟩
  let y := Function.argminOn (fun x => IsDiscreteValuationRing.addVal R (res R φ x)) s hs
  have hy : y ∈ s := Function.argminOn_mem _ _ hs
  refine ⟨⟨y, le_antisymm ?_ ?_⟩⟩
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; exact Submodule.zero_mem _
    rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact dvd_of_res_dvd R φ hy.2
      (IsDiscreteValuationRing.addVal_le_iff_dvd.1 (Function.argminOn_le (fun x => IsDiscreteValuationRing.addVal R (res R φ x)) s ⟨hx, hx0⟩))
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy.1

theorem mem_of_prime {q : Ideal ((intRing R).comap φ)} (hq : q.IsPrime) (hq0 : q ≠ ⊥)
    (a : (intRing R).comap φ) : a ∈ q ↔ ¬ IsUnit (res R φ a) := by
  constructor
  · intro ha hu
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q ha (isUnit_of_isUnit_res R φ hu))
  · intro hna
    obtain ⟨y, hyq, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
    have hry : res R φ y ≠ 0 := fun h => hy0 (res_injective R φ (by rw [h, map_zero]))
    have hfin : IsDiscreteValuationRing.addVal R (res R φ y) ≠ ⊤ :=
      fun h => hry (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
    set N := (IsDiscreteValuationRing.addVal R (res R φ y)).toNat with hN
    have h1 : 1 ≤ IsDiscreteValuationRing.addVal R (res R φ a) :=
      ENat.one_le_iff_ne_zero.2 fun h => hna (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
    have hle : IsDiscreteValuationRing.addVal R (res R φ y) ≤
        IsDiscreteValuationRing.addVal R (res R φ (a ^ N)) := by
      rw [map_pow, IsDiscreteValuationRing.addVal_pow, ← ENat.coe_toNat hfin, ← hN]
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • IsDiscreteValuationRing.addVal R (res R φ a) := nsmul_le_nsmul_right h1 N
    have hd := dvd_of_res_dvd R φ hy0 (IsDiscreteValuationRing.addVal_le_iff_dvd.1 hle)
    exact hq.mem_of_pow_mem N (Ideal.mem_of_dvd _ hd hyq)

end General

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow.OrdRing

section Order

variable {B C : Type} [CommRing B] [IsDomain B] [Field C] (ev : B →+* C) (t : B)

theorem exists_pow_mul_not_dvd (hfin : ∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) {b : B}
    (hb : b ≠ 0) : ∃ (n : ℕ) (c : B), b = t ^ n * c ∧ ¬ t ∣ c := by
  obtain ⟨n, hn⟩ := hfin b hb
  have hf : FiniteMultiplicity t b := ⟨n, fun h => hn ((pow_dvd_pow t (Nat.le_succ n)).trans h)⟩
  obtain ⟨c, hc, hnd⟩ := hf.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, hc, hnd⟩

theorem ker_eq_span (hker : ∀ b, ev b = 0 ↔ t ∣ b) : RingHom.ker ev = Ideal.span {t} := by
  ext b; rw [RingHom.mem_ker, Ideal.mem_span_singleton, hker]

theorem map_ker_eq_span (hker : ∀ b, ev b = 0 ↔ t ∣ b) :
    IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker ev)) =
      Ideal.span {algebraMap B (Localization.AtPrime (RingHom.ker ev)) t} := by
  have h := congrArg (Ideal.map (algebraMap B (Localization.AtPrime (RingHom.ker ev))))
    (ker_eq_span ev t hker)
  rw [Ideal.map_span, Set.image_singleton] at h
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ev)]
  exact h

theorem isDVR (ht : t ≠ 0) (hker : ∀ b, ev b = 0 ↔ t ∣ b)
    (hfin : ∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) :
    IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker ev)) := by
  set P := RingHom.ker ev
  have hinj : Function.Injective (algebraMap B (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have ht' : algebraMap B (Localization.AtPrime P) t ≠ 0 :=
    fun h => ht (hinj (by rw [h, map_zero]))
  have htprime : Prime (algebraMap B (Localization.AtPrime P) t) := by
    rw [← Ideal.span_singleton_prime ht', ← map_ker_eq_span ev t hker]
    infer_instance
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, htprime.irreducible, fun {x} hx => ?_⟩
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
  have hb : b ≠ 0 := by rintro rfl; exact hx (IsLocalization.mk'_zero _)
  obtain ⟨n, c, rfl, hc⟩ := exists_pow_mul_not_dvd t hfin hb
  have hcP : c ∈ P.primeCompl := fun h => hc ((hker c).1 (RingHom.mem_ker.1 h))
  have hu := IsLocalization.map_units (Localization.AtPrime P) (⟨c, hcP⟩ : P.primeCompl)
  have hs := IsLocalization.map_units (Localization.AtPrime P) s
  refine ⟨n, hu.unit * hs.unit⁻¹, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, Units.val_mul, IsUnit.unit_spec, map_mul, map_pow,
    _root_.mul_assoc, _root_.mul_assoc, hs.val_inv_mul, _root_.mul_one]

noncomputable def evLoc : Localization.AtPrime (RingHom.ker ev) →+* C :=
  IsLocalization.lift (M := (RingHom.ker ev).primeCompl) (g := ev)
    fun y => isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)

theorem evLoc_algebraMap (b : B) :
    evLoc ev (algebraMap B (Localization.AtPrime (RingHom.ker ev)) b) = ev b :=
  IsLocalization.lift_eq _ _

theorem evLoc_eq_zero_iff (hker : ∀ b, ev b = 0 ↔ t ∣ b)
    (z : Localization.AtPrime (RingHom.ker ev)) : evLoc ev z = 0 ↔ ¬ IsUnit z := by
  constructor
  · intro h hu; exact (hu.map (evLoc ev)).ne_zero h
  · intro hz
    have hm : z ∈ IsLocalRing.maximalIdeal _ := hz
    rw [map_ker_eq_span ev t hker, Ideal.mem_span_singleton] at hm
    obtain ⟨c, rfl⟩ := hm
    rw [map_mul, evLoc_algebraMap, (hker t).2 dvd_rfl, zero_mul]

end Order

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow.OrdRing

theorem exists_of_dvr (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (i : A →+* Ω)
    (hf : Function.Injective f) (hi : Function.Injective i)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (j : B →+* R)
    (hj : Function.Injective j) (ev' : R →+* C) (hev : ∀ b, ev' (j b) = ev b)
    (hzero : ∀ z, ev' z = 0 ↔ ¬ IsUnit z) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W)
      (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C),
      Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧
      (∀ a, i₁ a ≠ 0 → IsUnit a) ∧
      ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  have hg : Function.Injective ((algebraMap R (FractionRing R)).comp (j.comp f)) :=
    (IsFractionRing.injective R (FractionRing R)).comp (hj.comp hf)
  let φ : FractionRing A →+* FractionRing R := IsFractionRing.lift hg
  let V := (intRing R).comap φ
  haveI : IsPrincipalIdealRing V := isPrincipalIdealRing_comap R φ
  have hmemA : ∀ a : A, algebraMap A (FractionRing A) a ∈ V := fun a => by
    rw [ValuationSubring.mem_comap, IsFractionRing.lift_algebraMap]
    exact ⟨j (f a), rfl⟩
  let g : A →+* V := (algebraMap A (FractionRing A)).codRestrict V hmemA
  let i₀ : V →+* Ω := (IsFractionRing.lift hi).comp V.subtype
  have hi₀ : Function.Injective i₀ := fun x y h => Subtype.ext ((IsFractionRing.lift hi).injective h)
  have hres : ∀ a : A, res R φ (g a) = j (f a) := fun a => by
    apply IsFractionRing.injective R (FractionRing R)
    rw [algebraMap_res]
    exact IsFractionRing.lift_algebraMap hg a
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, g, i₀,
    ev'.comp (res R φ), hi₀, ?_, ?_, ?_, ?_⟩
  · ext a
    exact IsFractionRing.lift_algebraMap hi a
  · ext a
    simp only [RingHom.comp_apply]
    rw [hres, hev]
  · intro a ha
    exact isUnit_of_isUnit_res R φ (not_not.1 fun h => ha ((hzero _).2 h))
  · intro q hq
    by_cases hq0 : q = ⊥
    · left; rw [hq0, (RingHom.injective_iff_ker_eq_bot _).1 hi₀]
    · right
      ext a
      rw [mem_of_prime R φ hq hq0, RingHom.mem_ker, RingHom.comp_apply, hzero]

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow

open GlobalTheory.MBLow.OrdRing in

theorem exists_localRing_of_order : ∀ (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (t : B) (i : A →+* Ω), Function.Injective f → Function.Injective i → t ≠ 0 → (∀ b, ev b = 0 ↔ t ∣ b) → (∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C), Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  intro A B C Ω _ _ _ _ _ _ f ev t i hf hi ht hker hfin
  haveI := isDVR ev t ht hker hfin
  exact exists_of_dvr A B C Ω f ev i hf hi (Localization.AtPrime (RingHom.ker ev))
    (algebraMap B _) (IsLocalization.injective _ (RingHom.ker ev).primeCompl_le_nonZeroDivisors)
    (evLoc ev) (evLoc_algebraMap ev) (evLoc_eq_zero_iff ev t hker)

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldFrameValueNeZeroOfComplex
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

namespace GlobalTheory.FrameDenseZ

open Formalism.L2.LamCM GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT in

theorem exists_poly_div_det_secZ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
    (e : Ix Dw → ℤ) (F : Rul Xo c) (hF : F ∈ GlobalTheory.AllWt.secZ Xo c e) :
    ∃ (P : MvPolynomial (FrVar Dw.mult) K) (N : ℕ), ∀ (S : Type) [CommRing S] [Algebra c.F S] (φ : K →ₐ[c.F] S)
      (z z' : FrPt Xo c S) (Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S)),
      (∀ b, IsUnit (Y b).det) → FrMap φ y z → FrChg (fun b => (Y b).transpose) 1 z z' →
      (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, hWD, -⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  obtain ⟨A, _, _, π, X, hred, hX, hA⟩ := GlobalTheory.LamT.RatFn.exists_genericRing c.F K (E →+* ℂ) Dw.mult
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c K A π y
  obtain ⟨u, hu, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A u₀ (fun b => (X b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  obtain ⟨P, N, hP⟩ := hA (evR Xo c F u)
  refine ⟨P, N, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  obtain ⟨k, hkπ, hkX, hk⟩ := hP S φ Y hY
  obtain ⟨w, hw⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c A S k u₀
  have hw' : FrMap (k.comp π) y w := frMap_trans (Xo := Xo) (c := c) _ _ _ π k y u₀ w hu₀ hw
  rw [hkπ] at hw'
  have hwz : w = z := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K S φ y).1 w z hw' hz
  subst hwz
  have hm : FrMap k u z' := by
    refine (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A S k u₀ u w z' _ _ hu hw).2 ?_
    have e : (fun τ => ((X τ).transpose).map k) = fun b => (Y b).transpose :=
      funext fun b => by rw [Matrix.transpose_map, hkX]
    rw [e, Units.val_one, map_one]
    exact hz'
  rw [evR_frMap hWD F hF.1 k u (hT _ u) z' hm]
  exact hk

end GlobalTheory.FrameDenseZ

namespace GlobalTheory.FrameDenseZ

open Formalism.L2.LamCM in

theorem exists_frame_evalFr_ne_zero {K : Type} [Field K] [Infinite K] {B : Type} [Fintype B] (m : B → ℕ)
    (P : MvPolynomial (FrVar m) K) (hP : P ≠ 0) :
    ∃ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K, (∀ b, (Y b).det ≠ 0) ∧ evalFr P Y ≠ 0 := by
  classical
  have hD : ∀ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b ≠ 0 := by
    intro b h
    have := GlobalTheory.LamT.FieldPoly.evalFr_blockDetPoly (K := K) m b (fun _ => 1)
    rw [h] at this
    simp [evalFr] at this
  have hQ : P * ∏ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b ≠ 0 :=
    mul_ne_zero hP (Finset.prod_ne_zero_iff.2 fun b _ => hD b)
  obtain ⟨v, hv⟩ : ∃ v : FrVar m → K,
      MvPolynomial.eval v (P * ∏ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hQ (MvPolynomial.funext fun x => by simp only [h x, map_zero])
  let Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := fun b => Matrix.of fun i j => v ⟨b, (j, i)⟩
  have hY : ∀ R : MvPolynomial (FrVar m) K, evalFr R Y = MvPolynomial.eval v R := fun R => rfl
  rw [map_mul, map_prod] at hv
  refine ⟨Y, fun b => ?_, ?_⟩
  · rw [← GlobalTheory.LamT.FieldPoly.evalFr_blockDetPoly m b Y, hY]
    exact (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hv)) b (Finset.mem_univ b)
  · rw [hY]
    exact left_ne_zero_of_mul hv

theorem exists_frame_evR_ne_zero_of_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K]
    (y : FrPt Xo c K) (e : Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ (σ : c.F →+* ℂ) (σ₁ : K →ₐ[c.F] CAt σ)
    (w : FrPt Xo c (CAt σ)), spMap σ₁.toRingHom ≫ y.x = w.x → evR Xo c F w ≠ 0 →
    ∃ y' : FrPt Xo c K, y'.x = y.x ∧ evR Xo c F y' ≠ 0 := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y e F hF σ σ₁ w hw hne
  classical
  obtain ⟨P, N, hP⟩ := exists_poly_div_det_secZ E H Dw l Xo c K y e F hF
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hP0 : P ≠ 0 := by
    intro hP0
    haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
    haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c K _ σ₁ y
    obtain ⟨g, s, hg, hzw⟩ :=
      (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c _ z w).1 (hw.symm.trans hz.1.symm)
    obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g 1 hg
    obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z1 (fun _ => 1) s (fun _ => by simp)
    have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c _ z z1 z2).2 _ _ _ _ h1 h2
    simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
    have e' : z2 = w := (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g s hg).unique h3 hzw
    subst e'
    let t : Ix Dw → (CAt σ)ˣ := fun i => match i with
      | none => s
      | some _ => 1
    have hb : FrBor t z1 z2 := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c _ z1 z2 z2).1 t).2
      ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => Matrix.one_apply_eq i, h2⟩
    have hv := hP _ σ₁ z z1 (fun b => (g b).transpose)
      (fun b => by rw [Matrix.det_transpose]; exact hg b) hz
      (by simpa only [Matrix.transpose_transpose] using h1)
    rw [hP0, map_zero] at hv
    have hz1 : evR Xo c F z1 = 0 := by
      have hdet : (∏ b, ((g b).transpose).det) ^ N ≠ 0 :=
        pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun b _ => by
          rw [Matrix.det_transpose]; exact (hg b).ne_zero)
      have h00 : Formalism.L2.LamCM.evalFr (0 : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) (CAt σ))
          (fun b => (g b).transpose) = 0 := by simp [Formalism.L2.LamCM.evalFr]
      rw [h00] at hv
      exact (mul_eq_zero.1 hv).resolve_left hdet
    apply hne
    rw [GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF (CAt σ) t z1 z2 hb, hz1, mul_zero]
  obtain ⟨Y, hYd, hYv⟩ := exists_frame_evalFr_ne_zero Dw.mult P hP0
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (Y b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact (hYd b).isUnit)
  refine ⟨y', hy'.1, fun h0 => hYv ?_⟩
  have hv := hP K (AlgHom.id c.F K) y y' Y (fun b => (hYd b).isUnit)
    (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K K (AlgHom.id c.F K) y).2.1 hy'
  rw [h0, mul_zero, show (AlgHom.id c.F K).toRingHom = RingHom.id K from rfl, MvPolynomial.map_id] at hv
  exact hv.symm

end GlobalTheory.FrameDenseZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefFromBlocks
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl.BlockPos

theorem exists_neg_mul_le {n : Type} [Fintype n] (S : Matrix n n ℝ) :
    ∃ C : ℝ, ∀ x : n → ℝ, -(C * (x ⬝ᵥ x)) ≤ x ⬝ᵥ S *ᵥ x := by
  refine ⟨∑ i, ∑ j, |S i j|, fun x => ?_⟩
  have h : ∀ i, x i * x i ≤ x ⬝ᵥ x := fun i =>
    Finset.single_le_sum (f := fun i => x i * x i) (fun _ _ => mul_self_nonneg _) (Finset.mem_univ i)
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib, mulVec, dotProduct, dotProduct, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hi := h i
  have hj := h j
  rw [dotProduct] at hi hj
  rcases abs_cases (S i j) with ⟨e, p⟩ | ⟨e, p⟩ <;> rw [e]
  · nlinarith [mul_nonneg p (sq_nonneg (x i + x j)), mul_le_mul_of_nonneg_left hi p, mul_le_mul_of_nonneg_left hj p]
  · have p' : 0 ≤ -S i j := by linarith
    nlinarith [mul_nonneg p' (sq_nonneg (x i - x j)), mul_le_mul_of_nonneg_left hi p', mul_le_mul_of_nonneg_left hj p']

theorem exists_posDef_fromBlocks {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {Y : Matrix m m ℝ} (hY : Y.PosDef) (P : Matrix m n ℝ) {Q B : Matrix n n ℝ} (hQ : Q.IsHermitian) (hB : B.PosDef) :
    ∃ T : ℝ, ∀ t : ℝ, T < t → (fromBlocks Y P Pᴴ (Q + t • B)).PosDef := by
  obtain ⟨c, hc, hcB⟩ := posDef_exists_mul_dotProduct_le hB
  obtain ⟨C, hC⟩ := exists_neg_mul_le (Q - Pᴴ * Y⁻¹ * P)
  have : Invertible Y := (isUnit_iff_isUnit_det Y).mpr (hY.det_pos.ne').isUnit |>.invertible
  refine ⟨max 0 (C / c), fun t ht => ?_⟩
  have ht0 : 0 < t := (le_max_left _ _).trans_lt ht
  have htC : C < t * c := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt ht)
  have hH : (Q + t • B).IsHermitian := hQ.add (hB.smul ht0).1
  refine PosDef.of_dotProduct_mulVec_pos (hY.1.fromBlocks rfl hH) fun x hx => ?_
  rw [← Sum.elim_comp_inl_inr x, dotProduct_mulVec, schur_complement_eq₁₁ P _ _ _ hY.1, ← dotProduct_mulVec,
    ← dotProduct_mulVec]
  by_cases h2 : x ∘ Sum.inr = 0
  · have h1 : x ∘ Sum.inl ≠ 0 := fun h1 => hx (by rw [← Sum.elim_comp_inl_inr x, h1, h2]; simp)
    simpa [h2] using hY.dotProduct_mulVec_pos h1
  · refine add_pos_of_nonneg_of_pos (hY.posSemidef.dotProduct_mulVec_nonneg _) ?_
    have e : Q + t • B - Pᴴ * Y⁻¹ * P = (Q - Pᴴ * Y⁻¹ * P) + t • B := by abel
    rw [e, star_trivial, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul]
    have a1 := hC (x ∘ Sum.inr)
    have a2 := mul_le_mul_of_nonneg_left (hcB (x ∘ Sum.inr)) ht0.le
    have a3 : 0 < (x ∘ Sum.inr) ⬝ᵥ (x ∘ Sum.inr) := by
      simpa using (dotProduct_star_self_pos_iff (v := x ∘ Sum.inr)).mpr h2
    nlinarith [mul_pos (sub_pos.mpr htC) a3]

theorem full_posDef : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ (k : ℕ) (β : N.Form k), ∃ T : ℝ, ∀ w : ℂ, T < w.im →
    (w • bmat bX β).IsSymm ∧ (d.full σ (w • bmat bX β)).IsSymm ∧
      ((d.full σ (w • bmat bX β)).map Complex.im).PosDef := by
  intro N g' r g bX d σ k β
  have hB := (ClassMin.realExtension_posDef_iff _ bX).mp (ClassMin.realExtension_ofIntBilin_posDef β.symm β.pos)
  have hQ : (d.t22.map Complex.im).IsHermitian := by
    ext i j
    simp [d.toricPeriodBlock_isSymm.apply i j]
  obtain ⟨T, hT⟩ := exists_posDef_fromBlocks d.pos (d.t12.map Complex.im) hQ hB
  refine ⟨T, fun w hw => ?_⟩
  have hs : (w • bmat bX β).IsSymm := by
    ext i j
    simp [bmat, β.symm (bX j) (bX i)]
  refine ⟨hs, (IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hs)).submatrix σ, ?_⟩
  convert (hT w.im hw).submatrix σ.injective using 1
  ext i j
  simp only [CD.full, map_apply, submatrix_apply]
  rcases σ i with a | a <;> rcases σ j with b | b <;> simp [bmat, ClassMin.polar_ofIntBilin β.symm]

end GlobalTheory.MBLow.Cl.BlockPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarMatrixBetweenKeyData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.TwoData

theorem exists_scalar_matrix : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (th th' : P.L.Sec) (v v' : Fin P.g → (epsR K ⟶ P.A)), (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th) → (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th') → IsLieBasis v → IsLieBasis v' → ∃ (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), a ≠ 0 ∧ (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) ∧ ∀ i, IsLieComb (M i) v (v' i) := by
  intro K _ P th th' v v' hth hth' hv hv'
  obtain ⟨b, hb⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.principalPolarisation_exists_unique_section GlobalTheory.abelianSchemeLaws_all.2.secTwist P
  obtain ⟨a, ha, -⟩ := hb th
  obtain ⟨a', ha', -⟩ := hb th'
  choose M hM using fun i => (hv.2 _ (hv'.1 i)).exists
  have hne : ∀ (s : P.L.Sec) (c : K), (∀ s' : Sp K, ∃ z : P.A.left, P.A.hom z = s' ∧ z ∈ Out.nonzeroLocus s) →
      (∀ i, s.f i = Geo.Tor.constFn P.A.hom _ c * b.f i) → c ≠ 0 := by
    rintro s c hs hc rfl
    obtain ⟨z, -, hz⟩ := hs (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    rw [hc i, Geo.Tor.constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  have h0 := hne th a hth ha
  have h0' := hne th' a' hth' ha'
  refine ⟨a' * a⁻¹, M, mul_ne_zero h0' (inv_ne_zero h0), fun i => ?_, hM⟩
  rw [ha' i, ha i, ← _root_.mul_assoc, Geo.Tor.constFn, Geo.Tor.constFn, Geo.Tor.constFn, ← map_mul, ← map_mul, inv_mul_cancel_right₀ h0]

end GlobalTheory.MBLow.TwoData
end

