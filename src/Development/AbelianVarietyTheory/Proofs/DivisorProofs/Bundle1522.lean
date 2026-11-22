import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1499
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
section
open MvPolynomial NumberField Module GlobalTheory.AllWt GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.CompRestr

open GlobalTheory.FlatLine GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem idem_mem_sec (Z : Comp Xo c) : idem Z ∈ sec Xo c 0 0 := by
  rw [← secZ_nat]
  have : (fun i => (ex Dw (0 : (E →+* ℂ) × ℕ → ℕ) 0 i : ℤ)) = 0 := by
    funext i
    rcases i with _ | ⟨τ, i⟩ <;> simp [ex]
  rw [this]
  exact idem_mem_secZ Z

theorem idem_mul_mem_cuspW {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (Z : Comp Xo c) {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspW Xo c U G) : idem Z * f ∈ cuspW Xo c U G := by
  rw [mem_cuspW] at hf ⊢
  refine ⟨?_, fun σ hσ => ?_⟩
  · have := mul_mem_secZ (idem_mem_secZ Z) hf.1
    rwa [zero_add] at this
  · rw [AllWt.rdU_mul]
    refine IdemCusp.mul_mem_holSub (U σ).X (modelWt (U σ) G) (rdU (U σ) (idem Z)) (fun k => ?_) (hf.2 σ hσ)
    have hD : Dom (E := E) 0 0 := ⟨fun τ _ _ _ => le_rfl, Even.zero⟩
    have hs := (hU σ hσ).2.2.2.2.1 0 0 hD (idem Z) (idem_mem_sec Z) k
    have h0 : laU (U σ) 0 0 k = 0 := by
      funext τ j
      simp [laU]
    rw [h0] at hs
    refine IdemCusp.isIdemFn_of_isSec _ hs ?_
    have := congrFun (AllWt.rdU_mul (U σ) (idem Z) (idem Z)) k
    rw [idem_mul_idem] at this
    exact this.symm

theorem exists_cuspOn_restrict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (Z : Comp Xo c) (G : WTZ E) (f : cuspW Xo c U G), ∃ g : cuspOn U Z G, (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c g y = evR Xo c f y) ∧ (f ∈ latW U G → g ∈ latOn U Z G) := by
  intro E _ _ _ H Dw l Xo c r U hU Z G f
  have hs : idem Z * (f : Rul Xo c) ∈ suppOn Z := by
    rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  refine ⟨⟨idem Z * (f : Rul Xo c), idem_mul_mem_cuspW hU Z f.2, hs⟩, fun S _ _ y hy => ?_, fun hf => ?_⟩
  · show evR Xo c (idem Z * (f : Rul Xo c)) y = evR Xo c f y
    by_cases ht : Tested y
    · have e : evR Xo c (idem Z * (f : Rul Xo c)) y = evR Xo c (idem Z) y * evR Xo c f y :=
        evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (idem Z) f y
      rw [e, evR_idem hy ht, one_mul]
    · unfold evR evalAt
      rw [dif_neg ht, dif_neg ht]
  · refine (mem_supLat_iff (Z := Z) hs).2 fun la v hv => ?_
    show 0 ≤ v (idem Z * (f : Rul Xo c))
    rw [(isVal_valOn hv).mul, val_idem hv, zero_add]
    exact hf la v (valOn_subset Z la hv)

end GlobalTheory.CompRestr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.PrincData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isIntegral_cc {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map ((IsCMField.complexConj E : E →+* E).toIntAlgHom)

theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, cc, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E) :
    herm G (c • x) y = (c : E) * herm G x y := by
  simp only [herm, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def, show algebraMap (𝓞 E) E c = (c : E) from rfl]; ring

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E) :
    herm G x (c • y) = cc (c : E) * herm G x y := by
  simp only [herm, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def]
  simp only [cc, map_mul]
  ring

theorem exists_nat_herm_int (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (hL : L.FG) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ ((n : E) * herm G x y) := by
  classical
  obtain ⟨s, rfl⟩ := hL
  obtain ⟨y0, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ((s ×ˢ s).image fun p => herm G p.1 p.2)
  have hgen : ∀ a ∈ s, ∀ b ∈ s, IsIntegral ℤ ((y0 : E) * herm G a b) := fun a ha b hb => by
    have h := hy _ (Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, rfl⟩)
    rwa [zsmul_eq_mul] at h
  have hright : ∀ a ∈ s, ∀ y ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)),
      IsIntegral ℤ ((y0 : E) * herm G a y) := by
    intro a ha y hy'
    induction hy' using Submodule.span_induction with
    | mem b hb => exact hgen a ha b hb
    | zero => simpa [herm, cc] using isIntegral_zero
    | add u v _ _ hu hv => rw [herm_add_right, mul_add]; exact hu.add hv
    | smul c u _ hu => rw [herm_smul_right, mul_left_comm]; exact (isIntegral_cc c.2).mul hu
  have hall : ∀ x ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)), ∀ y ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)),
      IsIntegral ℤ ((y0 : E) * herm G x y) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha => exact hright a ha
    | zero => intro y _; simpa [herm] using isIntegral_zero
    | add u v _ _ hu hv => intro y hy'; rw [herm_add_left, mul_add]; exact (hu y hy').add (hv y hy')
    | smul c u _ hu => intro y hy'; rw [herm_smul_left, mul_left_comm]; exact c.2.mul (hu y hy')
  refine ⟨y0.natAbs, Int.natAbs_pos.2 hy0, fun x hx y hy' => ?_⟩
  have key := hall x hx y hy'
  rcases Int.natAbs_eq y0 with h | h
  · have e : ((y0.natAbs : ℕ) : E) = (y0 : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_natCast] at h'
      exact h'.symm
    rw [e]; exact key
  · have e : ((y0.natAbs : ℕ) : E) = -(y0 : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_neg, Int.cast_natCast] at h'
      rw [h', neg_neg]
    rw [e, neg_mul]; exact key.neg

theorem exists_nat_int (k : E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * k) := by
  have halg : IsAlgebraic ℤ k := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨y, hy, hyi⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hyi
  rcases Int.natAbs_eq y with h | h
  · have e : ((y.natAbs : ℕ) : E) = (y : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_natCast] at h'
      exact h'.symm
    rw [e]; exact hyi
  · have e : ((y.natAbs : ℕ) : E) = -(y : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_neg, Int.cast_natCast] at h'
      rw [h', neg_neg]
    rw [e, neg_mul]; exact hyi.neg

theorem exists_princ_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (M : ℕ) (X0 : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)), 3 ≤ M → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ X : Data E r, X.Gm = X0.Gm ∧ X.Ψ = X0.Ψ ∧ X.p0 = X0.p0 ∧ X.Λ = Λ ∧ ∀ γ, γ ∈ X.Γ ↔ IsUStab X0.Gm Λ γ ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y := by
  intro E _ _ _ r M X0 Λ hM hfg hsp
  obtain ⟨n, hn, hnint⟩ := exists_nat_herm_int X0.Gm Λ hfg
  obtain ⟨k, hk, hkint⟩ := exists_nat_int X0.κ0
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ,
      IsIntegral ℤ (((M * n * k : ℕ) : E) / (M : E) * X0.κ0 * herm X0.Gm x y) := by
    intro x hx y hy
    have e : ((M * n * k : ℕ) : E) / (M : E) * X0.κ0 * herm X0.Gm x y =
        ((k : E) * X0.κ0) * ((n : E) * herm X0.Gm x y) := by
      push_cast
      field_simp
    rw [e]
    exact hkint.mul (hnint x hx y hy)
  obtain ⟨X, hΨ, hG, hp, hΛ, -, -, -, hΓ, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski E r X0.p0 M (M * n * k)
    X0.Ψ X0.Gm Λ X0.ξ0 X0.κ0 X0.cmType X0.Gm_herm X0.Gm_det X0.p0_le
    (fun τ hτ => X0.signature ⟨τ, hτ⟩) hfg hsp hM X0.ξ0_im X0.ξ0_ne X0.κ0_xi
    (fun τ hτ => X0.κ0_sign ⟨τ, hτ⟩) (by positivity) hint
  refine ⟨X, hG, hΨ, hp, hΛ, fun γ => ?_⟩
  rw [hΓ γ]
  refine and_congr Iff.rfl (forall₂_congr fun x _ => exists_congr fun y => and_congr Iff.rfl ?_)
  exact sub_eq_iff_eq_add'.symm

end GlobalTheory.PrincData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeComplexMumfordBundleOriginStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_free_complex_structureSheaf_cech_origin : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), L.IsLB → IsProjBy A.hom → (∃ t : LB.Gen (Theta A L), t.IsGen) → IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → (∀ (T : Over (Sp K)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∃ (J : Ideal (A.left.presheaf.stalk x₀)) (C : CochainComplex (ModuleCat.{0} (A.left.presheaf.stalk x₀)) ℕ) (φ : A.left.presheaf.stalk x₀ →+* K), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) ∧ RingHom.ker φ = IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ∧ (∀ i, Module.Free (A.left.presheaf.stalk x₀) (C.X i) ∧ Module.Finite (A.left.presheaf.stalk x₀) (C.X i)) ∧ (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧ Nonempty ((Module.Dual (A.left.presheaf.stalk x₀) (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A.left.presheaf.stalk x₀] (A.left.presheaf.stalk x₀ ⧸ J)) ∧ (∀ p : PrimeSpectrum (A.left.presheaf.stalk x₀), ∃ (K' : Type) (_ : Field K') (φ' : A.left.presheaf.stalk x₀ →+* K'), RingHom.ker φ' = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ∨ g < i) → (((ModuleCat.extendScalars φ').mapHomologicalComplex _).obj C).ExactAt i) ∧ ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ i, Nonempty (((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i) ≃ₗ[K] (cechLB A.hom (LB.triv A.left) D).homology i) := by
  first | exact @GlobalTheory.MumfordLocalComplex.exists_ideal_free_complex_at_origin | exact GlobalTheory.MumfordLocalComplex.exists_ideal_free_complex_at_origin | (intros; apply GlobalTheory.MumfordLocalComplex.exists_ideal_free_complex_at_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralElementCharPolyNonsplit
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ExInertUnit

theorem globalForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ M G : Matrix (Fin n) (Fin n) E, M.charpoly = P ∧ IsUnit G ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G := GlobalTheory.T.exists_hermitian_form_char_poly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem eventually_mem_integers (a : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) a ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) a).2

theorem mem_KGL_of_entries (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w n := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem entries_of_mem_KGL {w : Pl E} {k : GLw n w} (hk : k ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    k.val i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨a, rfl⟩ := hk
  exact (a.val i j).2

theorem mul_entries {w : Pl E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E) (hB : ∀ i j, B i j ∈ w.adicCompletionIntegers E)
    (i j : Fin n) : (A * B) i j ∈ w.adicCompletionIntegers E := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

set_option maxHeartbeats 800000 in

theorem local_step (hE : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (M G : Matrix (Fin n) (Fin n) E)
    (hG : IsUnit G) (hGh : cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G)
    (hMG : cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G)
    (hM : ∀ i j, algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E)
    (hG1 : ∀ i j, algebraMap E (w.adicCompletion E) (G i j) ∈ w.adicCompletionIntegers E)
    (hG2 : ∀ i j, algebraMap E (w.adicCompletion E) (G⁻¹ i j) ∈ w.adicCompletionIntegers E) :
    ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = M.charpoly.map (algebraMap E (w.adicCompletion E)) := by
  obtain ⟨-, -, hv, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hE w
  obtain ⟨hconj, ⟨ϖ, q, hU, -⟩, -⟩ := hns hw
  let f := algebraMap E (w.adicCompletion E)
  let c := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hcT : ∀ A : Matrix (Fin n) (Fin n) E, cT (cj w) (f.mapMatrix A) = f.mapMatrix (cT c A) := by
    intro A
    refine Matrix.ext fun i j => ?_
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
    exact hconj _
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hGu : IsUnit (f.mapMatrix G) := hG.map _
  have hginv : ((hGu.unit)⁻¹ : GLw n w).val = f.mapMatrix G⁻¹ := by
    have h : f.mapMatrix G⁻¹ * f.mapMatrix G = 1 := by
      rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
    exact Matrix.inv_eq_left_inv h
  have hgK : hGu.unit ∈ GlobalTheory.LFun.KGL w n :=
    mem_KGL_of_entries w _ (fun a b => by rw [IsUnit.unit_spec]; exact hG1 a b)
      (fun a b => by rw [hginv]; exact hG2 a b)
  have hgh : cT (cj w) hGu.unit.val = hGu.unit.val := by
    rw [IsUnit.unit_spec, hcT, hGh]
  obtain ⟨k, hk, hkk⟩ := GlobalTheory.LFun.InertChart.exists_norm hU hgK hgh
  have hMu : IsUnit M := by
    have h : (G⁻¹ * cT c M * G) * M = 1 := by
      have h' := hMG
      simp only [Matrix.mul_assoc] at h' ⊢
      rw [h', Matrix.nonsing_inv_mul _ hdet]
    exact (Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse h)
  have hMwu : IsUnit (f.mapMatrix M) := hMu.map _
  have hmG : cT (cj w) hMwu.unit.val * hGu.unit.val * hMwu.unit.val = hGu.unit.val := by
    rw [IsUnit.unit_spec, IsUnit.unit_spec, hcT, ← map_mul, ← map_mul, hMG]
  have hkinv : cT (cj w) (k⁻¹ : GLw n w).val * cT (cj w) k.val = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  set γ0 : GLw n w := k * hMwu.unit * k⁻¹ with hγ0
  have hγU : cT (cj w) γ0.val * 1 * γ0.val = 1 := by
    calc cT (cj w) γ0.val * 1 * γ0.val
        = cT (cj w) (k⁻¹ : GLw n w).val * (cT (cj w) hMwu.unit.val * (cT (cj w) k.val * k.val) * hMwu.unit.val)
            * (k⁻¹ : GLw n w).val := by
          rw [hγ0, Units.val_mul, Units.val_mul, cT_mul, cT_mul]
          simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = cT (cj w) (k⁻¹ : GLw n w).val * (cT (cj w) k.val * k.val) * (k⁻¹ : GLw n w).val := by
          rw [hkk, hmG]
      _ = 1 := by
          simp only [← Matrix.mul_assoc]
          rw [hkinv, Matrix.one_mul, Units.mul_inv]
  have hγUL : γ0 ∈ UL n w := by
    rw [UL, if_neg hw]
    exact hγU
  refine ⟨⟨γ0, hγUL⟩, ?_, ?_⟩
  · rw [KL, Subgroup.mem_subgroupOf]
    have hinv : cT (cj w) γ0.val = (γ0⁻¹ : GLw n w).val := by
      rw [Matrix.coe_units_inv]
      exact (Matrix.inv_eq_left_inv (by simpa using hγU)).symm
    have hint : ∀ a b, γ0.val a b ∈ w.adicCompletionIntegers E := by
      intro a b
      rw [hγ0, Units.val_mul, Units.val_mul]
      refine mul_entries (mul_entries (entries_of_mem_KGL hk) (fun i j => ?_))
        (entries_of_mem_KGL (inv_mem hk)) a b
      rw [IsUnit.unit_spec]
      exact hM i j
    refine mem_KGL_of_entries w γ0 hint (fun a b => ?_)
    rw [← hinv]
    have h0 := hint b a
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h0 ⊢
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [hv]
    exact h0
  · show (k.val * hMwu.unit.val * (k⁻¹ : GLw n w).val).charpoly = _
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj, IsUnit.unit_spec]
    exact Matrix.charpoly_map M f

theorem exists_integral_unitary_charpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  intro E _ _ _ hE n _ P hP
  obtain ⟨M, G, hMP, hG, hGh, hMG⟩ := globalForm E n P hP
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_mem_integers _
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (G i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_mem_integers _
  have h3 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (G⁻¹ i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_mem_integers _
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3 hw
  obtain ⟨γ, hγ, hc⟩ := local_step hE w hw M G hG hGh hMG hw1 hw2 hw3
  exact ⟨γ, hγ, by rw [hc, hMP]⟩

end GlobalTheory.ExInertUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviOfUnit
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.DescB.PlaneTwo
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.DescB.CentreTwoExists

open GlobalTheory.LeviLine Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_levi_of_unit (hcm : IsCMExt F E σ) {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁)
    (hskew : ∀ i j, σ (Y.J j i) = -Y.J i j) (hxx' : form σ Y.J H.x H.x = 0) (hyy' : form σ Y.J H.y H.y = 0)
    (hxy' : form σ Y.J H.x H.y = 1)
    (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) (t : (AE F E)ˣ) :
    ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) H t 1 m := by
  set c : AE F E →+* AE F E := (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom with hcdef
  have hc : ∀ r, c (c r) = r := cA_invol hcm
  have hJ : ∀ i j, c (incM F Y.J j i) = -incM F Y.J i j := by
    intro i j
    change cA σ (inclR (F := F) (AF F) (Y.J j i)) = -inclR (F := F) (AF F) (Y.J i j)
    rw [cA_inclR, hskew i j, map_neg]
  have hxx : sf c (incM F Y.J) (incV F H.x) (incV F H.x) = 0 := by rw [sf_inc, hxx', map_zero]
  have hyy : sf c (incM F Y.J) (incV F H.y) (incV F H.y) = 0 := by rw [sf_inc, hyy', map_zero]
  have hxy : sf c (incM F Y.J) (incV F H.x) (incV F H.y) = 1 := by rw [sf_inc, hxy', map_one]
  have hyx : sf c (incM F Y.J) (incV F H.y) (incV F H.x) = -1 := by rw [sf_skew c _ hc hJ, hxy, map_one]
  have hts : (t : AE F E) * c (c (↑t⁻¹ : AE F E)) = 1 := by rw [hc, Units.mul_inv]
  have hst : c (↑t⁻¹ : AE F E) * c (t : AE F E) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  let L := levi c (incM F Y.J) (incV F H.x) (incV F H.y)
  let g : GL (Fin n) (AE F E) :=
    ⟨L t (c ↑t⁻¹), L ↑t⁻¹ (c t), by
      rw [levi_mul hc hJ hxx hyy hxy, Units.mul_inv, ← map_mul, Units.inv_mul, map_one, levi_one],
      by rw [levi_mul hc hJ hxx hyy hxy, Units.inv_mul, ← map_mul, Units.mul_inv, map_one, levi_one]⟩
  have hg : g ∈ UG (cA σ) (incM F Y.J) := levi_unitary hc hJ hxx hyy hxy hts hst
  refine ⟨⟨g, hg⟩, ?_, ?_, ?_⟩
  · change L t (c ↑t⁻¹) *ᵥ incV F H.x = _
    rw [levi_mulVec, hxx, hxy]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change L t (c ↑t⁻¹) *ᵥ incV F H.y = c ↑t⁻¹ • incV F H.y
    rw [levi_mulVec, hyy, hyx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change L t (c ↑t⁻¹) * incM F H.ι = incM F H.ι * (1 : Matrix (Fin n₁) (Fin n₁) (AE F E))
    rw [Matrix.mul_one]
    refine ext_mulVec_single fun k => ?_
    have hcol : incM F H.ι *ᵥ Pi.single k 1 = incV F (H.ι *ᵥ Pi.single k 1) := by
      ext i
      simp [mulVec_single_one, incM, incV]
    rw [← mulVec_mulVec, hcol]
    exact levi_mulVec_of_orth _ _ _ _ (by rw [sf_inc, (horth _).1, map_zero]) (by rw [sf_inc, (horth _).2, map_zero])

theorem skew_chain (hcm : IsCMExt F E σ) (B : Base F E) {d d₁ p : ℕ} {W : Spc F E d}
    (hW : ∀ i j, σ (W.J j i) = -W.J i j) {H' : Plane E d d₁} {i₀ i₁ : ℕ} {sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)}
    {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} (hH : H'.IsAdapted σ B W (sp 0) i₀ i₁)
    (hiso : ∀ i < p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) :
    ∀ j ≤ p, ∀ k l, σ ((sp j).J l k) = -(sp j).J k l := by
  intro j
  induction j with
  | zero =>
    intro _ k l
    rw [← hH.gram]
    exact LeviFirst.gram_skew hcm _ _ hW k l
  | succ j ih =>
    intro hj k l
    rw [← (hiso j (by omega)).2.2.2.2.2.1]
    exact LeviFirst.gram_skew hcm _ _ (ih (by omega)) k l

end GlobalTheory.ThK.DescB.CentreTwoExists

namespace GlobalTheory.ThK.DescB

open GlobalTheory.ThK.DescB.CentreTwoExists Matrix

end GlobalTheory.ThK.DescB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfPolarisedGenericFibreStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_of_polarised_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → ∃ (σ : LB.Sec t.PP.L) (k : t.PP.L.ι), σ.f k ≠ 0 := by
  first | exact @GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt | exact GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt | (intros; apply GlobalTheory.ThetaDomain.exists_sec_ne_zero_of_polAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleMovedHeisenbergLatticePolynomialHeighStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scale_movedHeisenbergLattice_polynomial_heights : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (N : ℕ), 1 ≤ N →
    ∃ (C : ℝ) (k : ℕ), ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ m : ℕ, 1 ≤ m ∧
      (m : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ^ k ∧ ∀ i j : κ,
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j) ∧
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j) := by
  first | exact @GlobalTheory.MovedLat.exists_scale | exact GlobalTheory.MovedLat.exists_scale | (intros; apply GlobalTheory.MovedLat.exists_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroOnClosedFibreCompleteLocalStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonzero_on_closed_fibre_complete_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → CharZero R → ∀ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal R) D A G), ∃ θ : LB.Sec U.LG.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R := by
  first | exact @GlobalTheory.ThetaClosed.exists_section_nonzero_closed | exact GlobalTheory.ThetaClosed.exists_section_nonzero_closed | (intros; apply GlobalTheory.ThetaClosed.exists_section_nonzero_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharactersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_of_splittingCharacters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), (∃ η, IsEtaTilde D η) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ om, IsWeilDatumO ψ S T χS χT om := by
  first | exact @GlobalTheory.WeilExist.exists_isWeilDatumO | exact GlobalTheory.WeilExist.exists_isWeilDatumO | (intros; apply GlobalTheory.WeilExist.exists_isWeilDatumO <;> assumption)
end

