import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0169
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0807
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0792
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroInertiaOfLanglands
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

namespace GlobalTheory.DepthZeroBridge

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem redThrough_eq_of_val_sub_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l : ℕ} [Fact l.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar l) {a b : Ω} (ha : a ∈ A) (hab : A.valuation (a - b) < 1) :
    redThrough A κ a = redThrough A κ b := by
  have hab' : a - b ∈ A := (A.valuation_le_one_iff _).mp hab.le
  have hb : b ∈ A := by
    have : b = a - (a - b) := by ring
    rw [this]; exact A.sub_mem ha hab'
  unfold redThrough
  rw [dif_pos ha, dif_pos hb]
  congr 1
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  show (⟨a, ha⟩ - ⟨b, hb⟩ : A) ∈ IsLocalRing.maximalIdeal A
  exact (A.valuation_lt_one_iff _).mpr hab

open scoped Pointwise in

theorem depthZeroInertia_of_depthZeroTypeInertia : GlobalTheory.Published.DepthZeroTypeInertia → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.LocalLanglandsGL →
    GlobalTheory.Published.DepthZeroInertia := by
  intro HT HG HL
  intro E Ω _ _ _ _ _ g _ A w h rc hrc i hi κ L t ht hTC n σ _ τ P hP hinf
  have hn : 0 < n := hP.2.1.1
  obtain ⟨E', _, _, _, _, _, _, _, w', h', hg0, hg1, hN, ⟨ζ, hζ⟩, hfix⟩ := GlobalTheory.T.exists_unramified_totallyComplex_ext_with_unity_roots E Ω g A w h i hi n hn
  let t' : Ω ≃ₐ[E'] Ω := { t with commutes' := fun e => hfix t ht e }
  have htt : ∀ z, t' z = t z := fun _ => rfl
  have hdec : t' • A = A := by
    have h0 : t • A = A := ht.1
    ext z
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    conv_rhs => rw [← h0]
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    rfl
  have ht' : t' ∈ Ine (F := E') A := ⟨hdec, fun z hz => ht.2 z hz⟩
  have hres : AlgEquiv.restrictScalars E t' = t := by ext z; rfl
  obtain ⟨a', ha'⟩ : ∃ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' := by
    obtain ⟨rc', hrc', -⟩ := HL.1 E' Ω A w' h'
    obtain ⟨a', ha', -⟩ := hrc'
    exact ⟨a', ha'⟩
  obtain ⟨art, hart⟩ := HG E' Ω
  set u := a' (ineIncl h' ⟨t', ht'⟩) with hu_def
  have hu : IsUnitAt w' u := GlobalTheory.T.localArtin_inertia_isUnitAt h' a' ha' ⟨t', ht'⟩
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_integer_approx_unit_adicCompletion w' u hu
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hq : 0 < g ^ n - 1 := by
    have : 2 ≤ g ^ n := le_trans hg2 (Nat.le_self_pow hn.ne' g)
    omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) hq
  have hy' : y ^ (normV w' - 1) = algebraMap E' Ω ((((g : ℕ) : 𝓞 E')) : E') := by
    rw [hN, hy]; simp
  obtain ⟨σ', hσ'I, hσ'ab, hσ'v⟩ :=
    GlobalTheory.TameRecip.exists_ine_of_unit HG E' Ω art hart w' A h' ((g : ℕ) : 𝓞 E') hg0 hg1 y hy' u x hu hx
  have hab : toAb E' Ω σ' = toAb E' Ω t' := by
    rw [hσ'ab]; exact ha'.glob art hart _
  have hgE : ((g : ℕ) : E') ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  have hkum := GlobalTheory.T.kummerCharacter_factors_absoluteGaloisAbelianization E' Ω (g ^ n - 1) hq ζ hζ ((g : ℕ) : E') hgE y (by rw [hy, map_natCast]) σ' t' hab
  have hgΩ : ((g : ℕ) : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap E' Ω)]; exact (_root_.map_ne_zero _).mpr hgE
  have h1 := hTC n hn y hy
  have h2 : redThrough A κ (algebraMap E' Ω ((x : 𝓞 E') : E')) = L.gen n := by
    rw [← h1]
    have e : t y / y = σ' y / y := by rw [hkum]; rfl
    rw [e]
    exact (redThrough_eq_of_val_sub_lt_one A κ (tameQuot_mem A σ' hq hgΩ hy) hσ'v).symm
  haveI := w'.isMaximal
  letI : Field (𝓞 E' ⧸ w'.asIdeal) := Ideal.Quotient.field _
  have hgK : (((g : ℕ) : 𝓞 E' ⧸ w'.asIdeal)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w'.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hg0
  haveI : CharP (𝓞 E' ⧸ w'.asIdeal) g := (CharP.charP_iff_prime_eq_zero (Fact.out : g.Prime)).mpr hgK
  letI : Algebra (ZMod g) (𝓞 E' ⧸ w'.asIdeal) := ZMod.algebra _ g
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_residueField_embedding_place_over E' Ω g A w' h' κ
  have hcard : Nat.card (𝓞 E' ⧸ w'.asIdeal) = g ^ n := hN
  haveI : Finite (𝓞 E' ⧸ w'.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨θ, hreg, ⟨x0, hx0, hθ⟩, hprod⟩ := GlobalTheory.T.exists_regularCharacter_labelRoot_product g L n hn P hP.1 _ hcard ι
  have hιz : ι (Ideal.Quotient.mk _ x) = L.gen n := by rw [hι]; exact h2
  have hgen0 : L.gen n ≠ 0 := by
    intro e
    have ho := L.gen_order n hn
    rw [e, orderOf_eq_zero_iff'.mpr (fun k hk => by simp [zero_pow hk.ne'])] at ho
    omega
  have hz0 : (Ideal.Quotient.mk w'.asIdeal x) ≠ 0 := by
    intro e; rw [e, map_zero] at hιz; exact hgen0 hιz.symm
  set z : (𝓞 E' ⧸ w'.asIdeal)ˣ := Units.mk0 _ hz0 with hz
  have hform : ∀ y' : Gn g n, Irreducible (y' : Mt g n).charpoly → ∀ z' : (𝓞 E' ⧸ w'.asIdeal)ˣ,
      aeval (z' : 𝓞 E' ⧸ w'.asIdeal) (y' : Mt g n).charpoly = 0 →
      τ.character y' = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z' ^ g ^ j) : ℂˣ) : ℂ) := by
    intro y' hy' z' hz'
    have hmem : ι z' ∈ Formalism.CyclotomicNorms.rootsBar (y' : Mt g n).charpoly := by
      unfold Formalism.CyclotomicNorms.rootsBar
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Matrix.charpoly_monic _).ne_zero), Polynomial.IsRoot.def,
        Polynomial.eval_map]
      have hc : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) = ι.comp (algebraMap (ZMod g) (𝓞 E' ⧸ w'.asIdeal)) :=
        RingHom.ext_zmod _ _
      rw [hc, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hz', map_zero]
    rw [hP.2.2 x0 hx0 y' hy' (ι z') hmem]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hθ, Units.val_pow_eq_pow_val, map_pow]
  have H := (HT E E' Ω g A w h w' h' rc hrc i hi n hn hg1 hN a' ha' (𝓞 E' ⧸ w'.asIdeal) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective (Ideal.mk_ker) θ hreg τ hP.2.1 hform σ hinf).2 ⟨t', ht'⟩ x z rfl hx
  rw [← hres, H]
  exact hprod z hιz
end GlobalTheory.DepthZeroBridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentMapNonzeroOfSmallFieldForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.NX

noncomputable section

namespace GlobalTheory

theorem exists_desc_of_isKsForm : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), (S.A j).IsKsForm → ∀ (i : D.ntw.Tw) (b : Bool) (x : S.WL j), x ≠ 0 →
    ∃ Φ : S.WL j →+ Fm S i j b, Φ x ≠ 0 ∧
      (∀ (c : ↥D.LL0) (w : S.WL j), Φ (((c : ↥D.LL0) : D.what₂.LL) • w) = readLL0 S i b c • Φ w) ∧
      ∀ (T : Module.End D.what₂.LL (S.WL j)) (hT : ∀ w ∈ (S.A j).WK, T w ∈ (S.A j).WK) (w : S.WL j),
        Φ (T w) = Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)
          ((T.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hT) (Φ w) := by
  intro D S j hK i b x hx
  classical
  obtain ⟨n, v, hvK, hliK, hspK, hliL, hspL⟩ := hK
  let bL : Module.Basis (Fin n) D.what₂.LL (S.WL j) := Module.Basis.mk hliL (by rw [hspL])
  let bK0 : Module.Basis (Fin n) S.Ks (Submodule.span S.Ks (Set.range v)) := Module.Basis.span hliK
  let bK : Module.Basis (Fin n) S.Ks (FmK S j) := bK0.map (LinearEquiv.ofEq _ _ hspK)
  let ι : FmK S j →ₗ[S.Ks] S.WL j := (S.A j).WK.subtype
  have hbK : ∀ r, ι (bK r) = v r := by
    intro r
    show ((bK0 r : Submodule.span S.Ks (Set.range v)) : S.WL j) = v r
    exact congrArg Subtype.val (Module.Basis.span_apply hliK r)
  have hbL : ∀ r, bL r = v r := by intro r; simp [bL]
  let bF : Module.Basis (Fin n) (KB S i b) (Fm S i j b) := Algebra.TensorProduct.basis (KB S i b) bK
  obtain ⟨r0, ha⟩ : ∃ r0, bL.repr x r0 ≠ 0 := by
    by_contra h; push_neg at h; exact hx (bL.ext_elem fun r => by simpa using h r)
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ↥D.LL0 D.what₂.LL, g (bL.repr x r0) ≠ 0 := by
    by_contra h; push_neg at h; exact ha ((Module.forall_dual_apply_eq_zero_iff _ _).1 h)
  let f : D.what₂.LL →ₗ[↥D.LL0] ↥D.LL0 := (g (bL.repr x r0))⁻¹ • g
  have hfa : f (bL.repr x r0) = 1 := by simp [f, hg]
  have hfc : ∀ (c : ↥D.LL0) (y : D.what₂.LL), f ((c : D.what₂.LL) * y) = c * f y := by
    intro c y
    rw [show (c : D.what₂.LL) * y = c • y from (Algebra.smul_def c y).symm, map_smul, smul_eq_mul]
  let φ : (Fin n → D.what₂.LL) →+ (Fin n → KB S i b) :=
    AddMonoidHom.compLeft ((readLL0 S i b).toAddMonoidHom.comp f.toAddMonoidHom) (Fin n)
  let Φ : S.WL j →+ Fm S i j b :=
    (bF.equivFun.symm.toLinearMap.toAddMonoidHom).comp (φ.comp bL.equivFun.toLinearMap.toAddMonoidHom)
  have hΦ : ∀ w, bF.equivFun (Φ w) = fun r => readLL0 S i b (f (bL.repr w r)) := by
    intro w
    show bF.equivFun (bF.equivFun.symm (φ (bL.equivFun w))) = _
    rw [LinearEquiv.apply_symm_apply]; rfl
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro h0
    have := congrFun (hΦ x) r0
    rw [h0, map_zero, hfa, map_one] at this
    exact zero_ne_one this
  · intro c w
    apply bF.equivFun.injective
    rw [hΦ, bF.equivFun.map_smul, hΦ, bL.repr.map_smul]
    funext r
    simp only [Pi.smul_apply, smul_eq_mul, map_smul, Finsupp.smul_apply]
    rw [hfc, map_mul]
  · intro T hT w
    let T' : Module.End S.Ks (FmK S j) := (T.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hT
    let t := LinearMap.toMatrix bK bK T'
    have hTm : LinearMap.toMatrix bL bL T = t.map (algebraMap S.Ks D.what₂.LL) := by
      ext r q
      simp only [t, LinearMap.toMatrix_apply, Matrix.map_apply]
      have e1 : T (bL q) = ι (T' (bK q)) := by
        rw [hbL, ← hbK]; rfl
      have e2 : T (bL q) = ∑ s, (algebraMap S.Ks D.what₂.LL (bK.repr (T' (bK q)) s)) • bL s := by
        rw [e1]; conv_lhs => rw [← bK.sum_repr (T' (bK q))]
        rw [map_sum]; refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_smul, hbK, hbL, algebraMap_smul]
      rw [e2, Module.Basis.repr_sum_self]
    apply bF.equivFun.injective
    have hbc : Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) T' = LinearMap.baseChange (KB S i b) T' := rfl
    change bF.equivFun (Φ (T w)) = bF.equivFun (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) T' (Φ w))
    rw [hbc]
    have hMF : LinearMap.toMatrix bF bF (LinearMap.baseChange (KB S i b) T') = t.map (algebraMap S.Ks (KB S i b)) :=
      LinearMap.toMatrix_baseChange _ _ _ _
    have hL : ∀ r, bL.repr (T w) r = ∑ q, algebraMap S.Ks D.what₂.LL (t r q) * bL.repr w q := by
      intro r
      rw [← LinearMap.toMatrix_mulVec_repr bL bL T w, hTm]; rfl
    have hKB : ∀ r, bF.equivFun (LinearMap.baseChange (KB S i b) T' (Φ w)) r =
        ∑ q, algebraMap S.Ks (KB S i b) (t r q) * bF.equivFun (Φ w) q := by
      intro r
      have h1 := congrFun (LinearMap.toMatrix_mulVec_repr bF bF (LinearMap.baseChange (KB S i b) T') (Φ w)) r
      rw [hMF] at h1
      exact h1.symm
    funext r
    rw [hΦ, hKB, hΦ]
    simp only []
    rw [hL, map_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← S.kKs_spec, hfc, map_mul]; rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteUnramifiedApproximationPadic
section
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KurApprox
open Polynomial
variable {p : ℕ} [Fact p.Prime]

section Val

variable {K : Type} [Field K] [NumberField K] (ψ : K →+* ℂ_[p])

theorem valuation_eq_exp {x : K} (hx : x ≠ 0) :
    (placeAt ψ).valuation K x = WithZero.exp (-vLa (placeAt ψ) x) := by
  rw [vLa, neg_neg, WithZero.exp_log (((placeAt ψ).valuation K).ne_zero_iff.2 hx)]

theorem exists_uniformizer : ∃ π : K, π ≠ 0 ∧ vLa (placeAt ψ) π = 1 ∧ ‖ψ π‖ < 1 := by
  set P := placeAt ψ
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ1 : P.intValuation π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπn : ‖ψ (π : K)‖ < 1 := (mem_placeAt ψ π).1 ((P.intValuation_lt_one_iff_mem π).1 hπ1)
  have hνπ : P.valuation K (π : K) = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuation_of_algebraMap P π
  have hπ0 : (π : K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hνπ
    exact WithZero.exp_ne_zero hνπ.symm
  refine ⟨π, hπ0, ?_, hπn⟩
  simp [vLa, P, hνπ]

theorem norm_eq_zpow {π : K} (hπ0 : π ≠ 0) (hπ : vLa (placeAt ψ) π = 1) {x : K} (hx : x ≠ 0) :
    ‖ψ x‖ = ‖ψ π‖ ^ vLa (placeAt ψ) x := by
  set P := placeAt ψ
  set n := vLa P x
  set b := x * π ^ (-n) with hb
  have hb0 : b ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hπ0)
  have hνb : P.valuation K b = 1 := by
    rw [hb, map_mul, map_zpow₀, valuation_eq_exp ψ hx, valuation_eq_exp ψ hπ0, hπ, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg, n]
    rw [show -vLa (placeAt ψ) x + vLa P x = 0 from neg_add_cancel _, WithZero.exp_zero]
  have h1 : ‖ψ b‖ ≤ 1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one ψ hνb.le
  have h2 : ‖ψ b⁻¹‖ ≤ 1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one ψ (by rw [map_inv₀, hνb, inv_one])
  have hpos : 0 < ‖ψ b‖ := norm_pos_iff.2 ((map_ne_zero ψ).2 hb0)
  have hb1 : ‖ψ b‖ = 1 := by
    rw [map_inv₀, norm_inv] at h2
    exact le_antisymm h1 ((inv_le_one₀ hpos).1 h2)
  have hxb : x = b * π ^ n := by
    rw [hb, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  rw [hxb, map_mul, norm_mul, hb1, one_mul, map_zpow₀, norm_zpow]

end Val

section Unram

variable {F F' : Type} [Field F] [NumberField F] [Field F'] [NumberField F'] [Algebra F F']

theorem vLa_eq_of_mem_kurC (φ : F →+* ℂ_[p]) (φ' : F' →+* ℂ_[p]) (hcomp : ∀ a, φ' (algebraMap F F' a) = φ a)
    (hk : ∀ x, φ' x ∈ kurC φ) (a : F) : vLa (placeAt φ') (algebraMap F F' a) = vLa (placeAt φ) a := by
  by_cases ha : a = 0
  · subst ha; simp [vLa]
  obtain ⟨π, hπ0, hπ, hπn⟩ := exists_uniformizer φ
  obtain ⟨π', hπ0', hπ', hπn'⟩ := exists_uniformizer φ'
  set c := ‖φ π‖ with hc
  set c' := ‖φ' π'‖ with hc'
  have hc0 : 0 < c := norm_pos_iff.2 ((map_ne_zero φ).2 hπ0)
  have hc0' : 0 < c' := norm_pos_iff.2 ((map_ne_zero φ').2 hπ0')
  obtain ⟨b, hb⟩ := GlobalTheory.KurValue.exists_norm_eq φ (hk π')
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, norm_zero] at hb
    exact hc0'.ne' hb
  have e1 : c' = c ^ vLa (placeAt φ) b := by rw [hc', hb, norm_eq_zpow φ hπ0 hπ hb0]
  have hι0 : algebraMap F F' π ≠ 0 := (_root_.map_ne_zero _).2 hπ0
  have e2 : c = c' ^ vLa (placeAt φ') (algebraMap F F' π) := by
    rw [hc, ← hcomp, norm_eq_zpow φ' hπ0' hπ' hι0]
  have hinj := zpow_right_injective₀ hc0 hπn.ne
  have hmk : vLa (placeAt φ) b * vLa (placeAt φ') (algebraMap F F' π) = 1 := by
    apply hinj
    change c ^ (_ * _) = c ^ (1 : ℤ)
    rw [zpow_mul, ← e1, ← e2, zpow_one]
  have hm : vLa (placeAt φ) b = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmk with h | h
    · exact h.1
    · exfalso
      rw [h.1, zpow_neg_one] at e1
      have : 1 < c⁻¹ := (one_lt_inv₀ hc0).2 hπn
      linarith
  rw [hm, zpow_one] at e1
  have hιa : algebraMap F F' a ≠ 0 := (_root_.map_ne_zero _).2 ha
  have e3 := norm_eq_zpow φ' hπ0' hπ' hιa
  rw [hcomp, norm_eq_zpow φ hπ0 hπ ha, ← hc, ← hc', e1] at e3
  exact (hinj e3).symm

end Unram

section Approx

variable {F : Type} [Field F] (φ : F →+* ℂ_[p])

def adjRoots (N : ℕ) : IntermediateField F (PAt φ) :=
  IntermediateField.adjoin F {x : PAt φ | x ^ N = 1}

theorem finite_roots {N : ℕ} (hN : 0 < N) : {x : PAt φ | x ^ N = 1}.Finite := by
  classical
  refine ((nthRoots N (1 : PAt φ)).toFinset.finite_toSet).subset fun x hx => ?_
  simpa [Polynomial.mem_nthRoots hN] using hx

theorem finiteDimensional_adjRoots {N : ℕ} (hN : 0 < N) : FiniteDimensional F (adjRoots φ N) := by
  haveI := (finite_roots φ hN).to_subtype
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  have h : x ^ N = 1 := hx
  exact IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)

theorem numberField_adjRoots [NumberField F] {N : ℕ} (hN : 0 < N) : NumberField (adjRoots φ N) := by
  haveI := finiteDimensional_adjRoots φ hN
  haveI : FiniteDimensional ℚ (adjRoots φ N) := Module.Finite.trans F (adjRoots φ N)
  constructor

theorem adjRoots_mono {N M : ℕ} (h : N ∣ M) : adjRoots φ N ≤ adjRoots φ M := by
  obtain ⟨k, rfl⟩ := h
  refine IntermediateField.adjoin.mono _ _ _ fun x hx => ?_
  have hx' : x ^ N = 1 := hx
  show x ^ (N * k) = 1
  rw [pow_mul, hx', one_pow]

theorem adjRoots_le_kurC {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (z : PAt φ) (hz : z ∈ adjRoots φ N) :
    toCp φ z ∈ kurC φ := by
  let Kt : IntermediateField F (PAt φ) :=
    (show Subfield (PAt φ) from kurC φ).toIntermediateField fun a => mem_kurC φ a
  have hle : adjRoots φ N ≤ Kt := by
    refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    have hx' : x ^ N = 1 := hx
    exact root_mem_kurC (p := p) φ hpN hx'
  exact hle hz

def kurAlg : Subfield ℂ_[p] where
  carrier := {z | ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (show PAt φ from z) ∈ adjRoots φ N}
  mul_mem' := by
    rintro x y ⟨N, hN, hpN, hx⟩ ⟨M, hM, hpM, hy⟩
    refine ⟨N * M, Nat.mul_pos hN hM, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      exacts [hpN h, hpM h]
    · exact mul_mem (adjRoots_mono φ (dvd_mul_right N M) hx) (adjRoots_mono φ (dvd_mul_left M N) hy)
  one_mem' := ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one, one_mem _⟩
  add_mem' := by
    rintro x y ⟨N, hN, hpN, hx⟩ ⟨M, hM, hpM, hy⟩
    refine ⟨N * M, Nat.mul_pos hN hM, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      exacts [hpN h, hpM h]
    · exact add_mem (adjRoots_mono φ (dvd_mul_right N M) hx) (adjRoots_mono φ (dvd_mul_left M N) hy)
  zero_mem' := ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one, zero_mem _⟩
  neg_mem' := by
    rintro x ⟨N, hN, hpN, hx⟩
    exact ⟨N, hN, hpN, neg_mem hx⟩
  inv_mem' := by
    rintro x ⟨N, hN, hpN, hx⟩
    exact ⟨N, hN, hpN, inv_mem hx⟩

theorem kurC_le : kurC φ ≤ (kurAlg φ).topologicalClosure := by
  refine Subfield.topologicalClosure_minimal _ (sup_le ?_ ?_) (Subfield.isClosed_topologicalClosure _)
  · rintro _ ⟨a, rfl⟩
    exact Subfield.le_topologicalClosure _ ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one,
      IntermediateField.algebraMap_mem _ a⟩
  · refine Subfield.topologicalClosure_minimal _ ?_ (Subfield.isClosed_topologicalClosure _)
    refine (Subfield.closure_le.2 ?_).trans (Subfield.le_topologicalClosure _)
    rintro ζ ⟨n, hn, hpn, hζ⟩
    exact ⟨n, hn, hpn, IntermediateField.subset_adjoin _ _ hζ⟩

end Approx

end GlobalTheory.KurApprox

namespace GlobalTheory.KurApprox

theorem kur_approx : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (n : ℕ)
    (y : Fin n → ℂ_[p]), (∀ s, y s ∈ kurC φ) → ∀ ε : ℝ, 0 < ε →
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra F F') (φ' : F' →+* ℂ_[p]),
      (∀ a, φ' (algebraMap F F' a) = φ a) ∧ (∀ a : F, vLa (placeAt φ') (algebraMap F F' a) = vLa (placeAt φ) a) ∧
      ∃ a' : Fin n → F', ∀ s, ‖y s - φ' (a' s)‖ < ε := by
  intro p _ F _ _ φ n y hy ε hε
  have h1 : ∀ s, ∃ z : ℂ_[p], ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (show PAt φ from z) ∈ adjRoots φ N ∧ ‖y s - z‖ < ε := by
    intro s
    have hs : y s ∈ closure ((kurAlg φ : Subfield ℂ_[p]) : Set ℂ_[p]) := kurC_le φ (hy s)
    obtain ⟨z, ⟨N, hN, hpN, hz⟩, hd⟩ := Metric.mem_closure_iff.1 hs ε hε
    exact ⟨z, N, hN, hpN, hz, by rwa [dist_eq_norm] at hd⟩
  choose z N hN hpN hz hd using h1
  set M := ∏ s, N s with hM
  have hM0 : 0 < M := Finset.prod_pos fun s _ => hN s
  have hpM : ¬ p ∣ M := by
    intro h
    obtain ⟨s, _, hs⟩ := ((Fact.out : p.Prime).prime.dvd_finsetProd_iff _).1 h
    exact hpN s hs
  let K := adjRoots φ M
  haveI : NumberField K := numberField_adjRoots φ hM0
  let φ' : K →+* ℂ_[p] := (toCp φ).comp (algebraMap K (PAt φ))
  have hcomp : ∀ a, φ' (algebraMap F K a) = φ a := fun a => rfl
  have hk : ∀ x : K, φ' x ∈ kurC φ := fun x => adjRoots_le_kurC φ hM0 hpM x x.2
  have hzM : ∀ s, (show PAt φ from z s) ∈ K := fun s =>
    adjRoots_mono φ (Finset.dvd_prod_of_mem N (Finset.mem_univ s)) (hz s)
  exact ⟨K, inferInstance, inferInstance, inferInstance, φ', hcomp, vLa_eq_of_mem_kurC φ φ' hcomp hk,
    fun s => ⟨z s, hzM s⟩, fun s => hd s⟩

end GlobalTheory.KurApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitSupportedRepFiniteUnitaryClass
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RankReps

set_option maxHeartbeats 1000000 in

theorem exists_rep_split_levJ : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ h ∈ GfC (Vc D j), ∃ (γ : GQ (Vc D j)) (s : Finset (Pl D.host.E)) (h' : GA D (Vc D j)) (k : (ρ.B i j b).levJ (ρ.tw i b 0 ∅ 1)), SplitSet s ∧ (∀ v ∈ s, ((ρ.bad i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) ∧ h' ∈ GfC (Vc D j) ∧ SuppAt (idem s) (Vc D j) h' ∧ finPt (Vc D j) h = Bridge.ratF (Vc D j) γ * finPt (Vc D j) h' * (k : Bridge.Gf (Vc D j)) := by
  intro D ρ hρ i j b h hh
  obtain ⟨N₀, hN₀, hK⟩ := GlobalTheory.LevFinCong.exists_finCong_lev D (Vc D j) (ρ.B i j b).F.βS
    ((ρ.B i j b).levS (ρ.tw i b 0 ∅ 1))
  have hbad : 0 < ρ.bad i := Nat.pos_of_ne_zero (hρ.bad_ne i)
  have hK' : ∀ k ∈ GfC (Vc D j), GlobalTheory.Member.FinCong (Vc D j) N₀ k → FWT.fin (Vc D j) k ∈ (ρ.B i j b).levJ (ρ.tw i b 0 ∅ 1) :=
    fun k hk hc => ((ρ.B i j b).finPt_mem_levJ _ hk).2 (hK k hk hc).1
  obtain ⟨h', ⟨hh', hs⟩, γ, k, e⟩ := GlobalTheory.SplitReps.exists_split_rep (Vc D j) hN₀ hK' hbad (finPt (Vc D j) h)
  have hsb := GlobalTheory.SplitReps.splitOffBad_of_suppSplit (Vc D j) (ρ.bad i) h' hh' hs
  obtain ⟨-, e', P, hP, hoff, hsupp⟩ := hsb
  refine ⟨γ, P, h', k, ⟨e', hP⟩, hoff, hh', ?_, e⟩
  rw [idem_eq hP]
  exact hsupp

end GlobalTheory.RankReps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicPointLatticeIsLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFull

theorem baseFrame_one_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (h : Lev.IsBaseFrame V β Λ 1) :
    (Λ : Set (Fin V.rank → D.host.E)) = L0c D V := by
  obtain ⟨-, -, -, h1, h2⟩ := h
  ext x
  constructor
  · intro hx
    simpa using h2 x hx
  · intro hx
    simpa using h1 x hx

theorem latAt_isLattice : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (h : GA D (Vc D j)), Submodule.IsLattice D.host.E ((ρ.B i j b).latAt (finPt (Vc D j) h)) := by
  intro D ρ hρ i j b h
  rw [GlobalTheory.LatAtHLat.latAt_eq_hLat D _ _ (ρ.B i j b) (baseFrame_one_eq _ _ _ (hρ.latS i j b))]
  exact GlobalTheory.RepsCompare.isLattice_hLat _ _

end GlobalTheory.LatFull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtensionStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie GlobalTheory.GoodPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCDVRFractionFieldReadingInCp_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∀ (T' : CDVR) (i : T.Fr →+* T'.Fr), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsFinExt T T' i → ∀ j : T'.Fr →+* ℂ_[p], j.comp i = k → IsReading φ T' (i.comp io) j := by
  first | exact @GlobalTheory.GeoTie.ReadExt.isReading_ext | exact GlobalTheory.GeoTie.ReadExt.isReading_ext | (intros; apply GlobalTheory.GeoTie.ReadExt.isReading_ext <;> assumption)
end

