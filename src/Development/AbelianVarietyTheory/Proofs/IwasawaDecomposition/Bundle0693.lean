import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0662
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianTorusAfterSeparable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeRowsEqDoubleCosetOperators
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersProjectiveModuleIntFinrank
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory

theorem finite_projective_int_of_ringOfIntegers :
    ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.Finite ℤ X ∧ Module.Projective ℤ X ∧ Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  intro E _ _ X _ _ _ _
  have hfin : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have hflat : Module.Flat ℤ X := Module.Flat.trans ℤ (𝓞 E) X
  have hfree : Module.Free ℤ X := inferInstance
  refine ⟨hfin, inferInstance, ?_⟩
  rw [finrank_int_eq_mul_of_finite (O := 𝓞 E), RingOfIntegers.rank]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsClassSetPresentationCoefficientMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory

theorem rowsClassPresLink : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → ∀ (cX : CoefA X.toD7.sp.X') (c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W), (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E), Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) → LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) → Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ → (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) → ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, (∀ x, P.coef x = c x) ∧ (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') ∧ ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'), P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (RowAd.decoAd X I t h)) :=
  GlobalTheory.T.coefficient_map_level_character_equivariant

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianTorusAfterSeparableStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_torus_after_separable : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap k k'))).obj G)) := by
  first | exact @GlobalTheory.exists_finite_separable_torusExtension | exact GlobalTheory.exists_finite_separable_torusExtension | (intros; apply GlobalTheory.exists_finite_separable_torusExtension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelDomainLowerBlockEqZeroOfLargeGap
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SiegelGap

theorem chain {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hS : GlobalTheory.RedTh.IsSiegel d u) :
    ∀ m : ℕ, ∀ i j : Fin n, (j : ℕ) = i + m → d i ≤ 4 ^ m * d j := by
  first
  | exact @_root_.GlobalTheory.SiegelChain.siegel_chain
  | exact _root_.GlobalTheory.SiegelChain.siegel_chain
  | (apply _root_.GlobalTheory.SiegelChain.siegel_chain <;> assumption)
  | (intros; apply _root_.GlobalTheory.SiegelChain.siegel_chain <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SiegelChain.siegel_chain <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SiegelChain.siegel_chain ..)

theorem chain_le {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hS : GlobalTheory.RedTh.IsSiegel d u)
    (i j : Fin n) (h : i ≤ j) : d i ≤ 4 ^ n * d j := by
  have h1 := chain hS ((j : ℕ) - i) i j (by have : (i:ℕ) ≤ j := h; omega)
  have hm : (4:ℝ) ^ ((j : ℕ) - i) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  calc d i ≤ 4 ^ ((j : ℕ) - i) * d j := h1
    _ ≤ 4 ^ n * d j := by gcongr; exact hS.nonneg j

theorem lowerBlock_eq_zero_of_gap : ∀ (n : ℕ) (K c : ℝ), ∃ R : ℝ, 1 ≤ R ∧ ∀ (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), GlobalTheory.RedTh.IsSiegel d u → (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (∀ i j, j < i → v i j = 0) → (∀ i j, |v i j| ≤ c) → (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K) → ∀ k k' : Fin n, (k' : ℕ) = k + 1 → R * d k < d k' → ∀ p q, q ≤ k → k' ≤ p → (u * A.map (Int.cast : ℤ → ℝ) * v) p q = 0 := by
  intro n K c
  set C : ℝ := (n : ℝ) ^ 2 * (|c| + 1) with hC
  set X : ℝ := (|K| + 1) * C ^ 2 with hX
  have hC0 : 0 ≤ C := by positivity
  have hX0 : 0 ≤ X := by positivity
  have h16 : (0:ℝ) ≤ 16 ^ n * X := by positivity
  refine ⟨16 ^ n * X + 1, by linarith, ?_⟩
  intro A d u v hS hd hvu huv hvl hvc hsum k k' hkk' hR p q hqk hkp
  set B : Matrix (Fin n) (Fin n) ℝ := A.map (Int.cast : ℤ → ℝ) with hB
  set Wm := u * B * v with hW

  have hratio : ∀ s t : Fin n, t ≤ k → k' ≤ s → X * d t < d s := by
    intro s t hts hks
    have h1 := chain_le hS t k hts
    have h2 := chain_le hS k' s hks
    have h4 : (0:ℝ) < 4 ^ n := by positivity
    have hdk := hd k
    have e16 : (16:ℝ) ^ n = 4 ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
    have : 4 ^ n * (X * d t) < 4 ^ n * d s := by
      calc 4 ^ n * (X * d t) ≤ 4 ^ n * (X * (4 ^ n * d k)) := by gcongr
        _ = 16 ^ n * X * d k := by rw [e16]; ring
        _ < (16 ^ n * X + 1) * d k := by nlinarith
        _ < d k' := hR
        _ ≤ 4 ^ n * d s := h2
    exact lt_of_mul_lt_mul_left this h4.le

  have hterm : ∀ s t : Fin n, d s / d t * Wm s t ^ 2 ≤ K := by
    intro s t
    have hnn : ∀ a b : Fin n, 0 ≤ d a / d b * Wm a b ^ 2 := fun a b =>
      mul_nonneg (div_nonneg (hd a).le (hd b).le) (sq_nonneg _)
    calc d s / d t * Wm s t ^ 2 ≤ ∑ q, d s / d q * Wm s q ^ 2 :=
          Finset.single_le_sum (f := fun q => d s / d q * Wm s q ^ 2) (fun q _ => hnn s q) (Finset.mem_univ t)
      _ ≤ ∑ p, ∑ q, d p / d q * Wm p q ^ 2 :=
          Finset.single_le_sum (f := fun p => ∑ q, d p / d q * Wm p q ^ 2)
            (fun p _ => Finset.sum_nonneg (fun q _ => hnn p q)) (Finset.mem_univ s)
      _ ≤ K := hsum
  have hWsmall : ∀ s t : Fin n, t ≤ k → k' ≤ s → C * |Wm s t| < 1 := by
    intro s t hts hks
    have hr := hratio s t hts hks
    have hdt := hd t
    have hXr : X < d s / d t := by rw [lt_div_iff₀ hdt]; exact hr
    have h1 : X * Wm s t ^ 2 ≤ K := le_trans (mul_le_mul_of_nonneg_right hXr.le (sq_nonneg _)) (hterm s t)
    have h2 : C ^ 2 * Wm s t ^ 2 < 1 := by
      have hK : K ≤ |K| := le_abs_self K
      by_contra hcon
      push_neg at hcon
      have : (|K| + 1) * 1 ≤ (|K| + 1) * (C ^ 2 * Wm s t ^ 2) := by gcongr
      nlinarith
    have h3 : (C * |Wm s t|) ^ 2 < 1 := by rw [mul_pow, sq_abs]; exact h2
    have h4 : 0 ≤ C * |Wm s t| := by positivity
    nlinarith
  have hrec : B = v * Wm * u := by
    rw [hW]; simp only [← Matrix.mul_assoc]
    rw [hvu, Matrix.one_mul, Matrix.mul_assoc, hvu, Matrix.mul_one]
  have hAzero : ∀ i j : Fin n, k' ≤ i → j ≤ k → A i j = 0 := by
    intro i j hi hj
    have hent : (A i j : ℝ) = ∑ t, (∑ s, v i s * Wm s t) * u t j := by
      have : B i j = (v * Wm * u) i j := by rw [← hrec]
      simpa [hB, Matrix.mul_apply] using this
    have hn : (0:ℝ) < (n:ℝ) ^ 2 := by have := Fin.pos i; positivity
    have key : ∀ s t : Fin n, |v i s * Wm s t * u t j| < 1 / (n:ℝ) ^ 2 := by
      intro s t
      by_cases hs : s < i
      · rw [hvl i s hs]; simp; positivity
      by_cases ht : j < t
      · rw [hS.lower t j ht]; simp; positivity
      push_neg at hs ht
      have hsm := hWsmall s t (le_trans ht hj) (le_trans hi hs)
      have hu1 : |u t j| ≤ 1 := by
        rcases eq_or_lt_of_le ht with h | h
        · rw [h, hS.diag]; simp
        · have := hS.upper t j h; linarith
      have hv1 : |v i s| ≤ |c| + 1 := by
        have := hvc i s; have := le_abs_self c; linarith
      rw [abs_mul, abs_mul]
      calc |v i s| * |Wm s t| * |u t j| ≤ (|c| + 1) * |Wm s t| * 1 := by gcongr
        _ < 1 / (n:ℝ) ^ 2 := by
          rw [lt_div_iff₀ hn]
          have : (|c| + 1) * |Wm s t| * 1 * (n:ℝ) ^ 2 = C * |Wm s t| := by rw [hC]; ring
          linarith
    have hbound : |(A i j : ℝ)| < 1 := by
      rw [hent]
      calc |∑ t, (∑ s, v i s * Wm s t) * u t j| = |∑ t, ∑ s, v i s * Wm s t * u t j| := by
            simp [Finset.sum_mul]
        _ ≤ ∑ t, ∑ s, |v i s * Wm s t * u t j| :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => Finset.abs_sum_le_sum_abs _ _)
        _ < ∑ t : Fin n, ∑ s : Fin n, 1 / (n:ℝ) ^ 2 :=
            Finset.sum_lt_sum_of_nonempty ⟨i, Finset.mem_univ _⟩ fun t _ =>
              Finset.sum_lt_sum_of_nonempty ⟨i, Finset.mem_univ _⟩ fun s _ => key s t
        _ = 1 := by
            have : (n:ℝ) ≠ 0 := by have := Fin.pos i; positivity
            simp; field_simp
    have : |A i j| < 1 := by exact_mod_cast hbound
    exact Int.abs_lt_one_iff.mp this
  rw [hW]
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : q < t
  · simp [hvl t q ht]
  push_neg at ht
  have hz : ∑ s, u p s * B s t = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s < p
    · simp [hS.lower p s hs]
    push_neg at hs
    simp [hB, hAzero s t (le_trans hkp hs) (le_trans ht hqk)]
  rw [hz, zero_mul]

end GlobalTheory.SiegelGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelPullbackDvrExtension
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.SiegLoc.PelUnif

theorem isUnifOf_pel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (g n : ℕ) (R : Type) [CommRing R] (ω : R →+* c.F) (F : SFam g n (zetaAway n))
    (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left)
    (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S), IsDedFrac ω → IsSiegPull s j G e κ C π →
    ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (χ : Sp W ⟶ C.X) (t : SAB H (Sp W)) (_ : SABMap t C.t χ)
      (P : PELUnif I t), Set.range (jK W ≫ χ) ⊆ Set.range C.j → ∃ π' : t.G.left ⟶ G.left, IsUnifOf F j e (χ ≫ π) π' P.U := by
  intro E _ _ _ H D l Xo c g n R _ ω F S s j G _ e κ C π hω hS W _ _ I χ t m P hr
  obtain ⟨mu, y, α, α₂, -, -, hμ, hy, hα, hsq, hlam, hφ⟩ := hS

  obtain ⟨⟨_, _⟩, _, _⟩ := hω
  letI : Algebra R c.F := ω.toAlgebra
  obtain ⟨-, -, -, hpre, hfl, -, -⟩ :=
    GlobalTheory.genericPart_dense_proOpen R c.F C.X (Xo.XF c) C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  haveI : IsPreimmersion C.j := hpre
  haveI : Flat C.j := hfl
  obtain ⟨y₀, hy₀⟩ := HomExt.exists_lift_of_range_subset C.j (jK W ≫ χ) hr

  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A t.G (jK W) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso P.U.gen.symm).comp
      (isGrpPullback_pullback t.G (jK W))).congr (Category.id_comp _) rfl
  have hA := gpG.comp m.cart
  let ψ : P.A.A.left ⟶ C.t.G.left := (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W)) ≫ m.φ
  have hw : ψ ≫ C.t.G.hom = (P.A.A.hom ≫ y₀) ≫ (C.jQ ≫ pullback.fst _ _) := by
    rw [hA.1.w]
    simp only [Category.assoc]
    rw [← hy₀]
    rfl
  let α₀ : P.A.A.left ⟶ C.oF.t.G.left := C.m.cart.1.lift ψ (P.A.A.hom ≫ y₀) hw
  have hα₀ : α₀ ≫ C.m.φ = ψ := C.m.cart.1.lift_fst _ _ _
  have hα₀' : α₀ ≫ C.oF.t.G.hom = P.A.A.hom ≫ y₀ := C.m.cart.1.lift_snd _ _ _
  have hB : IsGrpPullback P.A.A C.oF.t.G y₀ α₀ :=
    C.m.cart.cancel (hA.congr (hy₀.symm) hα₀.symm) hα₀'

  have hB' : IsGrpPullback P.A.A F.univ.A (y₀ ≫ y) (α₀ ≫ α) := hB.comp hα
  let U := lift (pushPt hB.1.w (fst P.A.A P.A.A)) (pushPt hB.1.w (snd P.A.A P.A.A))
  have hU₁ : U.left ≫ (fst C.oF.t.G C.oF.t.G).left = (fst P.A.A P.A.A).left ≫ α₀ := by
    rw [← Over.comp_left]
    exact congrArg (fun z => z.left) (lift_fst (pushPt hB.1.w (fst P.A.A P.A.A)) (pushPt hB.1.w (snd P.A.A P.A.A)))
  have hU₂ : U.left ≫ (snd C.oF.t.G C.oF.t.G).left = (snd P.A.A P.A.A).left ≫ α₀ := by
    rw [← Over.comp_left]
    exact congrArg (fun z => z.left) (lift_snd (pushPt hB.1.w (fst P.A.A P.A.A)) (pushPt hB.1.w (snd P.A.A P.A.A)))
  have hsq' : Geo.Tor.IsSquare (α₀ ≫ α) (U.left ≫ α₂) :=
    ⟨by rw [Category.assoc, hsq.1, ← Category.assoc, hU₁, Category.assoc],
     by rw [Category.assoc, hsq.2, ← Category.assoc, hU₂, Category.assoc]⟩

  have i₁ : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have i₀ : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have ext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK W))) := P.bundle ▸ P.U.ext
  have h₁ : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W))) :=
    LBIso.chartPull (chartPullSec P.A.L P.U.gen.hom.left P.U.gen.inv.left i₁)
      (chartPullSame t.PP.L (fun _ : PUnit => P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W))
        (fun _ => pullback.fst t.G.hom (jK W)) (fun _ => 1) P.U.gen.inv.left fun _ => rfl) ext
  have hm : LBIso t.PP.L (C.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hc : LBIso C.oF.t.PP.L (C.t.PP.L.pull C.m.φ) := by
    obtain ⟨w, hw, -⟩ := C.m.lin
    exact ⟨w, hw⟩
  have h₂ : LBIso (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK W))) (C.t.PP.L.pull ψ) :=
    LBIso.chartPull (chartPullPull t.PP.L _)
      (chartPullSame C.t.PP.L (fun _ : PUnit => ψ) (fun _ => m.φ) (fun _ => 1) _ fun _ => rfl) hm
  have h₃ : LBIso (C.oF.t.PP.L.pull α₀) (C.t.PP.L.pull ψ) :=
    LBIso.chartPull (chartPullPull C.oF.t.PP.L α₀)
      (chartPullSame C.t.PP.L (fun _ : PUnit => ψ) (fun _ => C.m.φ) (fun _ => 1) α₀ fun _ => hα₀.symm) hc
  have hL : LBIso P.A.L (C.oF.t.PP.L.pull α₀) :=
    LBIso.trans P.A.isLB (pull_isLB C.t.PP.isLB _) (pull_isLB C.oF.t.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB C.t.PP.isLB _) h₁ h₂) h₃.symm
  have hΛ₁ : LBIso (abelian₂ P.A.A P.A.L) (abelian₂ P.A.A (C.oF.t.PP.L.pull α₀)) :=
    GlobalTheory.PelPrim.lbIso_linComb hL _ _
  have hΛ₂ : LBIso (abelian₂ P.A.A (C.oF.t.PP.L.pull α₀)) (F.univ.P.pull (U.left ≫ α₂)) :=
    LBIso.chartPull
      (chartPullLinComb C.oF.t.PP.L α₀ _ _ _ U.left fun I => psum_push hB _ _ U (fun i => by
        fin_cases i
        · exact Over.OverMorphism.ext (by rw [Over.comp_left]; exact hU₁.symm)
        · exact Over.OverMorphism.ext (by rw [Over.comp_left]; exact hU₂.symm)) I.down)
      (chartPullSame F.univ.P (fun _ : PUnit => U.left ≫ α₂) (fun _ => α₂) (fun _ => 1) U.left fun _ => rfl) hlam
  have hΛ : LBIso (abelian₂ P.A.A P.A.L) (F.univ.P.pull (U.left ≫ α₂)) :=
    LBIso.trans (LB.isLB_linComb P.A.isLB _ _) (LB.isLB_linComb (pull_isLB C.oF.t.PP.isLB _) _ _)
      (pull_isLB F.univ.isLB _) hΛ₁ hΛ₂
  refine ⟨m.φ ≫ mu, m.cart.comp hμ, y₀ ≫ y, α₀ ≫ α, U.left ≫ α₂, ?_, hB', hsq', hΛ, ?_⟩
  · rw [Category.assoc, hy, ← Category.assoc, hy₀, Category.assoc]
  · rw [Category.assoc, ← hφ, ← Category.assoc α₀, hα₀]
    simp only [ψ, Category.assoc]
    rw [← Category.assoc P.U.gen.hom.left, i₀, Category.id_comp]

end GlobalTheory.SiegLoc.PelUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelUnipotentInverseEntriesBoundedStatement
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnipotent_inverse_entries_bounded : ∀ n : ℕ, ∃ c : ℝ, ∀ u : Matrix (Fin n) (Fin n) ℝ, (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ i j, i < j → |u i j| ≤ 1 / 2) → ∃ v : Matrix (Fin n) (Fin n) ℝ, v * u = 1 ∧ u * v = 1 ∧ (∀ i j, j < i → v i j = 0) ∧ ∀ i j, |v i j| ≤ c := by
  first | exact @GlobalTheory.siegel_unipotent_inv_bounded | exact GlobalTheory.siegel_unipotent_inv_bounded | (intros; apply GlobalTheory.siegel_unipotent_inv_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimplicialLabellingOfBarycentricStageZero
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.BaryFin

variable {X : Type} [AddCommGroup X]

theorem toReal_zero' : toReal (0 : LinearMap.BilinForm ℤ X) = 0 := LinearMap.ext₂ fun a b => by simp

theorem eq_zero_of_genRank_eq_zero {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (h : genRank γ = 0) (i : Fin m) :
    γ i = 0 := by
  unfold genRank at h
  haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  obtain ⟨a, ha, e⟩ := Module.finrank_eq_zero_iff.1 h ⟨γ i, Submodule.subset_span ⟨i, rfl⟩⟩
  have e' : a • γ i = 0 := congrArg Subtype.val e
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ e' y z
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this ⊢
  exact (mul_eq_zero.1 this).resolve_left ha

theorem inRCone_smul_iff {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) {k : ℕ}
    (hk : 0 < k) : InRCone γ ((k : ℤ) • β) ↔ InRCone γ β := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨fun i => c i / k, fun i => div_nonneg (hc i) hk'.le, LinearMap.ext₂ fun a b => ?_⟩
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at this ⊢
    push_cast at this
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, ← this]
    field_simp
  · rintro ⟨c, hc, h⟩
    refine ⟨fun i => k * c i, fun i => mul_nonneg hk'.le (hc i), LinearMap.ext₂ fun a b => ?_⟩
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at this ⊢
    push_cast
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

variable {O : Type} [CommRing O] {bar : O → O} {q : ℕ}

theorem eq_zero_of_label_nonpos {ψ lab : InvFun O} (hlab : IsCarrierDim bar q ψ lab) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q) {b : ℕ}
    {v : Fin b → LinearMap.BilinForm ℤ X} (hv : IsCell bar ψ v) (k : Fin b) (hk : lab.evalZ (v k) ≤ 0) : v k = 0 := by
  have key := hlab X hX (v k) (hv.mem k) (hv.nonneg k)
  rw [key] at hk
  have h0 := Nat.cast_nonpos.1 hk
  have hS : ({n : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ (v k) ∧
      genRank γ = n}).Nonempty := ⟨_, b, v, hv, inRCone_self v k, rfl⟩
  obtain ⟨m, γ, -, ⟨c, -, hc⟩, hr⟩ := Nat.sInf_mem hS
  rw [h0] at hr
  have hz := eq_zero_of_genRank_eq_zero γ hr
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ hc y z
  simp [hz, LinearMap.sum_apply] at this
  simpa using this

variable (O bar q) in

theorem simpLab_of_isBaryStage_zero (ψ lab φ : InvFun O) (hlab : IsCarrierDim bar q ψ lab)
    (hφ : IsBaryStage bar q ψ lab φ 0) : SimpLab bar q φ lab := by
  refine ⟨fun X _ _ _ _ hX β hβ hp k hk => ?_, fun X _ _ _ _ hX m γ hγ => ?_⟩
  · have hp' : ∀ y, 0 ≤ ((k : ℤ) • β) y y := fun y => by
      simp only [LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (hp y)
    rw [hlab X hX _ (Submodule.smul_mem _ _ hβ) hp', hlab X hX β hβ hp]
    simp only [inRCone_smul_iff _ _ hk]
  · obtain ⟨b, a, v, u, hc, hv, hin, hinj, -, hle, -, hli⟩ := hφ.2.2 X hX m γ hγ
    have hv0 : ∀ k, v k = 0 := fun k => eq_zero_of_label_nonpos hlab hX hv k
      (by simpa using hle (v k) (hv.mem k) (hv.nonneg k) (inRCone_self v k))
    have hu : IsCell bar φ u := by
      refine ⟨fun j => by simpa using hc.mem (Fin.natAdd b j), fun j => by simpa using hc.nonneg (Fin.natAdd b j),
        ?_, ?_⟩
      · have := linearOn_comp hc.linear (⟨Fin.natAdd b, fun x y h => by simpa using h⟩ : Fin a ↪ Fin (b + a))
        convert this using 1
        funext i
        exact (Fin.append_right v u i).symm
      · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hc.strict
        refine ⟨N, ℓ, hN, fun i => by simpa using h1 (Fin.natAdd b i), h2, fun β hβ hp he => ?_⟩
        obtain ⟨k, c, hk, hc'⟩ := h3 β hβ hp he
        refine ⟨k, fun i => c (Fin.natAdd b i), hk, ?_⟩
        rw [hc', Fin.sum_univ_add]
        simp [hv0]
    refine ⟨a, u, hu, Fintype.linearIndependent_iff.2 fun c hc0 i => congrFun (hli 0 c (by rw [hc0]; simp)) i,
      hinj, fun j => ?_⟩
    obtain ⟨c, hc0, h⟩ := hin j
    refine ⟨fun i => c (Fin.natAdd b i), fun i => hc0 _, ?_⟩
    rw [h, Fin.sum_univ_add]
    simp [hv0, toReal_zero']

example : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab φ : InvFun O), IsCarrierDim bar q ψ lab →
    IsBaryStage bar q ψ lab φ 0 → SimpLab bar q φ lab := fun O _ bar q => simpLab_of_isBaryStage_zero O bar q

end GlobalTheory.PolFan.BaryFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeRowsEqDoubleCosetOperatorsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitHecke_rows_eq_doubleCoset_operators : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') P ((famR X I hX U Xg tr).A.heckeR t) (fun i => 1 ≤ i.2 ∧ i.2 ≤ X.toD7.sp.X'.rank)
        (isTEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t))
        (isLocEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t))) := by
  first | exact @GlobalTheory.Mem.R3.RowHk.hecke_tie | exact GlobalTheory.Mem.R3.RowHk.hecke_tie | (intros; apply GlobalTheory.Mem.R3.RowHk.hecke_tie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkMapInjectiveBirational
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ChartBir

theorem isIso_stalkMap_j {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : GMod Xo c) (u : Xo.XF c) : IsIso (Y.j.stalkMap u) := by
  have hb : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 c.F)) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  have hbf : Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F)))
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have h2 : Flat (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip hbf
  haveI := Y.jQ_open
  have i1 : IsIso ((pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).stalkMap (Y.jQ u)) :=
    GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks _ _
  have i2 : IsIso (Y.jQ.stalkMap u) := (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 u
  show IsIso ((Y.jQ ≫ pullback.fst _ _).stalkMap u)
  rw [Scheme.Hom.stalkMap_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ i1 i2

theorem stalkMap_birational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s →
    ∀ z : Z.X, Function.Injective (π.stalkMap z).hom ∧ ∀ b : Z.X.presheaf.stalk z, ∃ a s : X.X.presheaf.stalk (π z),
      (π.stalkMap z).hom s ≠ 0 ∧ (π.stalkMap z).hom s * b = (π.stalkMap z).hom a := by
  intro E _ _ _ H D l Xo c X Z π hj _ z
  obtain ⟨hBd, -⟩ := Z.normal z
  obtain ⟨hAd, -⟩ := X.normal (π z)
  let p0 : PrimeSpectrum (Z.X.presheaf.stalk z) := ⟨⊥, Ideal.bot_prime⟩
  obtain ⟨w, hw⟩ := GlobalTheory.T.generic_stalk_point_in_interior E H D l Xo c Z z p0 rfl
  have hy : Z.j w ⤳ z := by
    have hm : Z.X.fromSpecStalk z p0 ∈ Set.range (Z.X.fromSpecStalk z) := ⟨p0, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hm
    rw [hw]; exact hm

  have hg : IsIso (π.stalkMap (Z.j w)) := by
    have h1 : IsIso ((Z.j ≫ π).stalkMap w) := by rw [hj]; exact isIso_stalkMap_j X w
    rw [Scheme.Hom.stalkMap_comp] at h1
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (isIso_stalkMap_j Z w) h1
  have hgb := (ConcreteCategory.isIso_iff_bijective (π.stalkMap (Z.j w))).1 hg
  have hπy : π (Z.j w) ⤳ π z := hy.map π.continuous

  have sq : ∀ a : X.X.presheaf.stalk (π z), (Z.X.presheaf.stalkSpecializes hy).hom ((π.stalkMap z).hom a) =
      (π.stalkMap (Z.j w)).hom ((X.X.presheaf.stalkSpecializes hπy).hom a) := fun a =>
    (Scheme.Hom.stalkSpecializes_stalkMap_apply π (Z.j w) z hy a).symm
  have hσ := GlobalTheory.PushInv.stalkSpecializes_injective (X := Z.X) hy
  have hτ := GlobalTheory.PushInv.stalkSpecializes_injective (X := X.X) hπy
  have hinj : Function.Injective (π.stalkMap z).hom := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => hτ ?_
    rw [map_zero]
    apply hgb.1
    rw [← sq, ha, map_zero, map_zero]
  refine ⟨hinj, fun b => ?_⟩
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X.X) (U := ⊤) (x := π z) trivial
  have hyU : π (Z.j w) ∈ U := hπy.mem_open U.2 hxU
  obtain ⟨κ, hκ⟩ := hgb.2 ((Z.X.presheaf.stalkSpecializes hy).hom b)
  obtain ⟨r, t, ht, e⟩ := GlobalTheory.PushInv.exists_frac hU hyU κ
  have er := GlobalTheory.PushInv.gs_specializes (𝟙 X.X) hπy U hxU r
  have et := GlobalTheory.PushInv.gs_specializes (𝟙 X.X) hπy U hxU t
  refine ⟨gs (𝟙 X.X) (π z) U r, gs (𝟙 X.X) (π z) U t, fun h0 => ?_, hσ ?_⟩
  · have h0' := hinj (h0.trans (map_zero _).symm)
    rw [h0', map_zero] at et
    rw [← et] at ht
    exact not_isUnit_zero ht
  · rw [map_mul, sq, sq, et, er, ← e, map_mul, hκ, mul_comm]

end GlobalTheory.ChartBir
end

