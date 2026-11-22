import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HermAdjoint

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero]; exact (u.ker 0).2 u.Λ.zero_mem
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

theorem exists_period_of_pow_eq_one {n : ℕ} (hn : 0 < n) {x : 𝟙_ (Over (Sp ℂ)) ⟶ A} (hx : x ^ n = 1) :
    ∃ a : u.Λ, u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) = x := by
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨⟨(n : ℂ) • z, (u.ker _).1 ((ex_nsmul u n z).trans hx)⟩, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]

theorem ex_period_pow {n : ℕ} (hn : 0 < n) (a : u.Λ) : u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) ^ n = 1 := by
  rw [← ex_nsmul, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]
  exact (u.ker _).2 a.2

theorem unitOn_injective {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) :=
  Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective

theorem int_eq_of_exp {p q : ℤ}
    (h : ∀ n : ℕ, 0 < n → Complex.exp (-(2 * Real.pi * Complex.I) * (p : ℂ) / n) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (q : ℂ) / n)) : p = q := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h ((q - p).natAbs + 1) (Nat.succ_pos _))
  have hn : (((q - p).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  have h₁ : ((q - p : ℤ) : ℂ) = ((m * (((q - p).natAbs + 1 : ℕ) : ℤ) : ℤ) : ℂ) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((q - p).natAbs + 1 : ℕ) : ℂ) = N at hm hn
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    field_simp at hm ⊢
    linear_combination hm
  have h₂ : (((q - p).natAbs + 1 : ℕ) : ℤ) ∣ q - p := ⟨m, by rw [mul_comm]; exact Int.cast_injective h₁⟩
  have h₃ := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h₂ (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem adjoint_of_im (Hm : Matrix (Fin g) (Fin g) ℂ) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ a ∈ s, ∀ b ∈ s, (hermForm Hm (F a) b).im = (hermForm Hm a (F' b)).im)
    (z w : Fin g → ℂ) : hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  have sl : ∀ (t : ℂ) a b, hermForm Hm (t • a) b = t * hermForm Hm a b := fun t a b => by
    simp [hermForm, smul_dotProduct]
  have sr : ∀ (t : ℝ) a b, hermForm Hm a ((t : ℂ) • b) = t * hermForm Hm a b := fun t a b => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
  have al : ∀ a a' b, hermForm Hm (a + a') b = hermForm Hm a b + hermForm Hm a' b := fun a a' b => by
    simp [hermForm, add_dotProduct]
  have ar : ∀ a b b', hermForm Hm a (b + b') = hermForm Hm a b + hermForm Hm a b' := fun a b b' => by
    simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  have all : ∀ a b, (hermForm Hm (F a) b).im = (hermForm Hm a (F' b)).im := fun a b => by
    have ha : a ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    have hb : b ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction ha, hb using Submodule.span_induction₂ with
    | mem_mem a b ha hb => exact h a ha b hb
    | zero_left b _ => simp [hermForm]
    | zero_right a _ => simp [hermForm]
    | add_left a a' b _ _ _ h₁ h₂ => rw [map_add, al, al, Complex.add_im, Complex.add_im, h₁, h₂]
    | add_right a b b' _ _ _ h₁ h₂ => rw [map_add, ar, ar, Complex.add_im, Complex.add_im, h₁, h₂]
    | smul_left t a b _ _ h₁ =>
      rw [← Complex.coe_smul, map_smul, sl, sl, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h₁]
    | smul_right t a b _ _ h₁ =>
      rw [← Complex.coe_smul, map_smul, sr, sr, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h₁]
  refine Complex.ext ?_ (all z w)
  have := all (Complex.I • z) w
  rwa [map_smul, sl, sl, Complex.I_mul_im, Complex.I_mul_im] at this

theorem lbIso_cubeLB_iff_hermForm : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (f f' : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) ↔ ∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) := by
  intro hl hl₂ hc hU P u Hm χ f f' F F' hAH hf hf' e e'
  have := P.isAb.comm
  obtain ⟨Ef, hE, -, -, -, -, -, -, hW⟩ := GlobalTheory.AnyAppellHumbert.isAH_properties hl hl₂ hc hU P u Hm χ hAH
  have hF : ∀ a : u.Λ, F a ∈ u.Λ := fun a => by rw [← u.ker, e, (u.ker _).2 a.2, MonObj.one_comp]
  have hF' : ∀ a : u.Λ, F' a ∈ u.Λ := fun a => by rw [← u.ker, e', (u.ker _).2 a.2, MonObj.one_comp]
  let c : ℤ → ℕ → ℂˣ := fun p n => Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (p : ℂ) / n))
  have w₁ : ∀ (n : ℕ) (a b : u.Λ), 0 < n → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ≫ f)
      (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn (c (Ef ⟨_, hF a⟩ b) n)) := fun n a b hn => by
    rw [← e, map_smul]
    exact hW n ⟨_, hF a⟩ b _ hn rfl
  have w₂ : ∀ (n : ℕ) (a b : u.Λ), 0 < n → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ)))
      (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ)) ≫ f') (unitOn (c (Ef a ⟨_, hF' b⟩) n)) := fun n a b hn => by
    rw [← e', map_smul]
    exact hW n a ⟨_, hF' b⟩ _ hn rfl
  have uq : ∀ (n : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) (d d' : Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ), x ^ n = 1 → y ^ n = 1 →
      Out.WeilIs P.A P.L n (x ≫ f) y d → Out.WeilIs P.A P.L n (x ≫ f) y d' → d = d' := fun n x y d d' hx hy h h' =>
    ((hl.weil _ P n _).1 _ _ (by rw [← MonObj.pow_comp, hx, MonObj.one_comp]) hy).unique h h'
  constructor
  · intro hiso
    obtain ⟨t, ht⟩ := GlobalTheory.NormRos.exists_gen_rosati P.isLB _ _ hiso
    have hR : Out.RosatiAdj P.A P.L f f' := fun _ =>
      ⟨⊤, trivial, LB.pullGen _ _ _ t _, DVR.pullGen_isGen _ _ _ _ ht _⟩
    refine adjoint_of_im Hm F F' _ u.full fun a ha b hb => ?_
    have : Ef ⟨_, hF ⟨a, ha⟩⟩ ⟨b, hb⟩ = Ef ⟨a, ha⟩ ⟨_, hF' ⟨b, hb⟩⟩ := int_eq_of_exp fun n hn => by
      have hx := ex_period_pow u hn ⟨a, ha⟩
      have hy := ex_period_pow u hn ⟨b, hb⟩
      exact congrArg Units.val (unitOn_injective (uq n _ _ _ _ hx hy (w₁ n ⟨a, ha⟩ ⟨b, hb⟩ hn)
        ((GlobalTheory.weilIs_rosati_iff hl.globalFns hl.cube P f f' hR n _ _ hx hy _).2 (w₂ n ⟨a, ha⟩ ⟨b, hb⟩ hn))))
    exact (hE ⟨_, hF ⟨a, ha⟩⟩ ⟨b, hb⟩).symm.trans ((congrArg Int.cast this).trans (hE _ _))
  · intro H
    refine GlobalTheory.lbIso_cubeLB_of_pairing_adjoint hl ℂ P f f' hf hf' fun n x y d hn hx hy hd => ?_
    obtain ⟨a, rfl⟩ := exists_period_of_pow_eq_one u hn hx
    obtain ⟨b, rfl⟩ := exists_period_of_pow_eq_one u hn hy
    have hab : Ef ⟨_, hF a⟩ b = Ef a ⟨_, hF' b⟩ := by
      apply Int.cast_injective (α := ℝ)
      rw [hE, hE]
      exact congrArg Complex.im (H a b)
    rw [uq n _ _ _ _ hx hy hd (w₁ n a b hn), hab]
    exact w₂ n a b hn

end GlobalTheory.HermAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEmbeddingSectionsOverField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.EmbField

theorem exists_section_spMap {K R' : Type} [Field K] [CommRing R'] (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ))
    (p : Sp K) (hp : p ∈ Set.range (spMap φ)) : ∃ ψ : R' →+* K, spMap ψ ≫ spMap φ = 𝟙 _ := by
  obtain ⟨a, -⟩ := hp
  have hsurj : Surjective (spMap φ) := ⟨fun q => ⟨a, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : IsIso (spMap φ) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hφ, hsurj⟩
  refine ⟨(Spec.preimage (inv (spMap φ))).hom, ?_⟩
  have hinv : spMap (Spec.preimage (inv (spMap φ))).hom = inv (spMap φ) := by
    simp [spMap]
  rw [hinv, IsIso.inv_hom_id]

private theorem projRep_map_of_secCoord_iff {A B σ : Type} [CommRing A] [CommRing B]
    (ψ : A →+* B) (φ : B →+* A) (hψ : spMap ψ ≫ spMap φ = 𝟙 (Sp B))
    {Z Z' : Scheme.{0}} {s : Z ⟶ Sp A} {s' : Z' ⟶ Sp B} (jz : Z' ⟶ Z) [IsIso jz]
    (hjz : jz ≫ s = s' ≫ spMap ψ) {M : LB Z} {M' : LB Z'} {th : σ → M.Sec} {th' : σ → M'.Sec}
    (hM' : M'.IsLB)
    (e : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Z') (w : σ → T),
      SecCoord M' th' y w ↔ SecCoord M th (y ≫ jz) w)
    {I : Ideal (MvPolynomial σ A)} (h : ProjRep I s M th) :
    ProjRep (I.map (MvPolynomial.map ψ)) s' M' th' := by
  obtain ⟨-, hpt, hex⟩ := h
  have hs' : s' = jz ≫ s ≫ spMap φ := by
    rw [reassoc_of% hjz, hψ, Category.comp_id]
  have hcomp : ∀ (T : Type) [CommRing T] (β : B →+* T), spMap β ≫ spMap ψ = spMap (β.comp ψ) := by
    intro T _ β
    exact (spMap_comp β ψ).symm
  have hker : ∀ (T : Type) [CommRing T] (β : B →+* T) (v : σ → T),
      (∀ F ∈ I, MvPolynomial.eval₂ (β.comp ψ) v F = 0) →
        ∀ F ∈ I.map (MvPolynomial.map ψ), MvPolynomial.eval₂ β v F = 0 := by
    intro T _ β v hv F hF
    have hle : I.map (MvPolynomial.map ψ) ≤ RingHom.ker (MvPolynomial.eval₂Hom β v) := by
      refine Ideal.map_le_iff_le_comap.2 fun G hG => ?_
      simp only [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
      exact hv G hG
    simpa [RingHom.mem_ker] using hle hF
  refine ⟨hM', fun T _ β x v hx hc => ?_, fun T _ β v hv hI => ?_⟩
  · have hx' : (x ≫ jz) ≫ s = spMap (β.comp ψ) := by
      rw [Category.assoc, hjz, ← Category.assoc, hx, hcomp]
    obtain ⟨hspan, hzero⟩ := hpt T (β.comp ψ) (x ≫ jz) v hx' ((e T x v).1 hc)
    exact ⟨hspan, hker T β v hzero⟩
  · have hI' : ∀ F ∈ I, MvPolynomial.eval₂ (β.comp ψ) v F = 0 := by
      intro F hF
      rw [← MvPolynomial.eval₂_map]
      exact hI _ (Ideal.mem_map_of_mem _ hF)
    obtain ⟨x₀, ⟨hx₀, hc₀⟩, hu⟩ := hex T (β.comp ψ) v hv hI'
    refine ⟨x₀ ≫ inv jz, ⟨?_, ?_⟩, fun y hy => ?_⟩
    · simp only [hs', Category.assoc, IsIso.inv_hom_id_assoc]
      rw [← Category.assoc, hx₀, ← hcomp, Category.assoc, hψ, Category.comp_id]
    · exact (e T _ v).2 (by rwa [Category.assoc, IsIso.inv_hom_id, Category.comp_id])
    · have hyx : y ≫ jz = x₀ :=
        hu _ ⟨by rw [Category.assoc, hjz, ← Category.assoc, hy.1, hcomp], (e T y v).1 hy.2⟩
      rw [← hyx, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem exists_emb_field : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (w : Ix g (N' ^ 2) → K), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh (𝟙 _) w → ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _)))), t.Emb m (Over.mk (𝟙 _)) σ ∧ ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ := by
  intro hL hL2 o _ g N' J b K _ s t m w hm h2 hth
  have hLB : (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))).IsLB := by
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.isLB _ _
  obtain ⟨R', _, φ, σ, hφ, hp, hE, hP⟩ :=
    GlobalTheory.T.exists_local_multiplicationPullback_theta_embedding hL hL2 o g N' J b (Sp K) s t m K (𝟙 _) w hm h2 hth (default : PrimeSpectrum K)
  obtain ⟨ψ, hψ⟩ := exists_section_spMap φ hφ _ hp
  let h : Over.mk (𝟙 (Sp K)) ⟶ Over.mk (spMap φ ≫ 𝟙 (Sp K)) := Over.homMk (spMap ψ) (by simpa using hψ)
  have hA1 : IsAffine (Over.mk (spMap φ ≫ 𝟙 (Sp K))).left :=
    show IsAffine (Spec (CommRingCat.of R')) from inferInstance
  have hA2 : IsAffine (Over.mk (𝟙 (Sp K))).left :=
    show IsAffine (Spec (CommRingCat.of K)) from inferInstance
  obtain ⟨σ', hE', hc⟩ := GlobalTheory.emb_baseChange hL2 o g N' J b (Sp K) s t m _ _ h σ hA1 hA2 hE
  refine ⟨σ', hE', ?_⟩
  have : IsIso (spMap φ) := by
    obtain ⟨a, -⟩ := hp
    exact (isIso_iff_isOpenImmersion_and_surjective _).2
      ⟨hφ, ⟨fun q => ⟨a, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩⟩
  have : IsIso (spMap ψ ≫ spMap φ) := by rw [hψ]; infer_instance
  have : IsIso (spMap ψ) := IsIso.of_isIso_comp_right (spMap ψ) (spMap φ)
  have : IsIso ((Over.forget (Sp K)).map h) := show IsIso (spMap ψ) from inferInstance
  have : IsIso h := isIso_of_reflects_iso h (Over.forget (Sp K))
  have : IsIso (h ▷ t.A).left := show IsIso ((Over.forget (Sp K)).map (h ▷ t.A)) from inferInstance
  have hsq := (GlobalTheory.EmbPull.isPullback_whisker t.A h).w
  have hP' := projRep_map_of_secCoord_iff ψ φ hψ (h ▷ t.A).left hsq hLB hc hP
  exact ideals_homogeneous.2.2 K _ _ _ _ _ _ hP'

end GlobalTheory.ZM.EmbField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicThetaConstantsPolarisedLattices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem exists_holomorphic_thetaConstants_of_family : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (d : ℕ) (B : Set (Fin d → ℂ)) (Q : (Fin d → ℂ) → (La →+ (Fin g → ℂ))) (Hm : (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ), Odd N' → Function.Bijective EF → IsOpen B → (∀ x, DifferentiableOn ℂ (fun bb => Q bb x) B) → (∀ bb ∈ B, (Function.Injective (Q bb) ∧ DiscreteTopology ((Q bb)).range ∧ Submodule.span ℝ (Set.range (Q bb)) = ⊤ ∧ ((Hm bb)).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Hm bb) z z).re) ∧ ∀ x y, (hermForm (Hm bb) ((Q bb) x) ((Q bb) y)).im = EF x y) ∧ ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q bb x) = Q bb (ac w x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → ∃ θ : (Fin d → ℂ) → Ix g (N' ^ 2) → ℂ, (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) ∧ ∀ bb ∈ B, ∀ t : TObj g (N' ^ 2) J b (spMap em), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q bb) x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q bb) (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q bb) x) = (Q bb) (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.HasTh (𝟙 _) (θ bb) := by
  intro hL hL2 _ hU o _ g N' J b em w w' La _ EF lam ac d B Q Hm hN hE hB hQ hpol hsum hadj
  rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · exact ⟨0, fun _ => differentiableOn_empty, fun _ h => absurd h (Set.notMem_empty _)⟩
  obtain ⟨hp₀, F₀, hF₀⟩ := hpol b₀ hb₀
  obtain ⟨hfree, hfin, -, halt⟩ :=
    unimodular_symplectic_coordinates_and_lattice_rank.2 La EF g (Q b₀) (Hm b₀) hp₀
  have hadd : ∀ x y, ac w (x + y) = ac w x + ac w y := fun x y => hp₀.1 (by
    rw [map_add, ← hF₀, ← hF₀, ← hF₀, map_add, map_add])
  let W : La →ₗ[ℤ] La := (AddMonoidHom.mk' (ac w) hadd).toIntLinearMap
  have hW : ∀ x, W x = ac w x := fun _ => rfl
  have hW' : ∀ x, (LinearMap.id - W : La →ₗ[ℤ] La) x = ac w' x := fun x => by
    rw [LinearMap.sub_apply, LinearMap.id_apply, hW, sub_eq_iff_eq_add', hsum]
  have hsemi := neg_one_zpow_form_apply_semicharacter La EF W (LinearMap.id - W) halt
    (add_sub_cancel _ _) (fun x y => by rw [hW, hW', hadj])
  simp only [hW] at hsemi
  obtain ⟨θ, hθ, hhol⟩ := HolTheta.exists_theta_holomorphic La EF
    (fun x => (-1 : ℂ) ^ EF x (ac w x)) g d N' B Q Hm hN.pos hE
    (fun x => by
      rcases Int.even_or_odd (EF x (ac w x)) with h | h
      · exact Or.inl h.neg_one_zpow
      · exact Or.inr h.neg_one_zpow)
    hsemi hB hQ (fun bb hb => (hpol bb hb).1)
  let x : Ix g (N' ^ 2) → La := fun a => ∑ i, ((a i).val : ℤ) • lam i
  refine ⟨fun z a => (-1 : ℂ) ^ EF (x a) (ac w (x a)) *
      (Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm (Hm z) (Q z (x a)) (Q z (x a))) *
        θ z ((N' : ℂ)⁻¹ • Q z (x a))), fun a => (hhol (x a)).const_mul _, ?_⟩
  rintro bb hb t ⟨u, χ', hAH, hΛ, hχ, hpt, -⟩
  obtain ⟨hne, hdiff, hfe⟩ := hθ bb hb
  let lam' : Fin (2 * g) → u.Λ := fun i => ⟨Q bb (lam i), (hΛ _).2 ⟨_, rfl⟩⟩
  have hth : u.IsThetaFn (Hm bb) χ' 1 (θ bb) := by
    refine ⟨hdiff, fun l z => ?_⟩
    obtain ⟨y, hy⟩ := (hΛ l).1 l.2
    rw [pow_one, hχ y l hy.symm, ← hy, hfe]
  have key := T.hasTh_eq_classicalThetaFunction_values hL hL2 hU o g N' J b em t u (Hm bb) χ' (θ bb) lam' hN hAH hth hne
    (fun i => by rw [hpt i, Nat.cast_pow])
  have hx : ∀ a : Ix g (N' ^ 2),
      ∑ i, ((a i).val : ℂ) • (lam' i : Fin g → ℂ) = Q bb (x a) := fun a => by
    simp only [x, lam', map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hx' : ∀ a : Ix g (N' ^ 2),
      χ' (∑ i, ((a i).val : ℤ) • lam' i) = (-1) ^ EF (x a) (ac w (x a)) := fun a => by
    refine hχ _ _ ?_
    simp only [x, lam', map_sum, map_zsmul, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
  simp only [hx, hx'] at key
  convert key using 2 with a
  exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecNeZeroOfLbIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleSpecialisation

theorem exists_sec_ne_zero_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (hs : ∃ s : LB.Sec B, ∃ j, s.f j ≠ 0) : ∃ s : LB.Sec A, ∃ j, s.f j ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨t, b, hb⟩ := hs
  refine ⟨DVR.secOfIso t hu hA hB, ?_⟩
  by_contra hn
  push Not at hn
  refine hb (fn_ext fun y hy => ?_)
  obtain ⟨a, ha⟩ := exists_chart hA y
  have e := (DVR.secOfIso_spec t hu hA hB a b).symm
  rw [hn a] at e
  have e' := (DVR.isoCand_rs u t a b le_rfl).symm.trans ((congrArg (DVR.rs le_rfl) (e.trans (map_zero _))).trans
    (map_zero _))
  have e'' := (Units.mul_right_eq_zero _).1 e'
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U a ⊓ B.U b := ⟨ha, hy⟩
  refine (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e'').trans ?_)
  rw [gs_eq _ y _ hm, gs_eq _ y _ hy, map_zero, map_zero, map_zero, map_zero]

theorem lbIso_pull_div_lbPow {X Y : Scheme.{0}} {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (f : Y ⟶ X) (a : ℕ) :
    LBIso ((LB.div (lbPow M a) L).pull f) (LB.div (lbPow (M.pull f) a) (L.pull f)) := by
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hp' : (lbPow (M.pull f) a).IsLB := LB.isLB_linComb (pull_isLB hM f) _ _
  refine (CechPic.cls_eq_iff (pull_isLB (LB.isLB_div hp hL) f) (LB.isLB_div hp' (pull_isLB hL f))).1 ?_
  rw [CechPic.cls_pull (LB.isLB_div hp hL), CechPic.cls_div hp hL, CechPic.cls_div hp' (pull_isLB hL f),
    CechPic.cls_lbPow hM, CechPic.cls_lbPow (pull_isLB hM f), CechPic.cls_pull hM, CechPic.cls_pull hL,
    map_sub, map_nsmul]

def baseChange {S S' : Scheme.{0}} (P : Out.PolAV S) (f : S' ⟶ S) : Out.PolAV S' where
  A := (Over.pullback f).obj P.A
  isAb := Out.TLinPf.isAb_pullback f P.A P.isAb
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (isGrpPullback_pullback P.A f).1 P.smoothDim
  L := P.L.pull (pullback.fst P.A.hom f)
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
  sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
  ktriv := by
    obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
    exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv

theorem relAmple_of_genericFibre : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsIntegral S] (P : Out.PolAV S) (M : LB P.A.left) (K : Type) [Field K] (x : Sp K ⟶ S), M.IsLB → Set.range x = {genericPoint S} → Out.RelAmple ((Over.pullback x).obj P.A) (M.pull (pullback.fst P.A.hom x)) → Out.RelAmple P.A M := by
  intro hL _ S _ _ P M K _ x hM hx hamp
  have hne : Nonempty (baseChange P x).A.left :=
    ⟨eSec (baseChange P x).A (Classical.arbitrary (Sp K))⟩
  obtain ⟨a, s, ha, hs⟩ := GlobalTheory.T.exists_sec_relAmplePow_div_ne_zero K (baseChange P x).A (baseChange P x).L (M.pull (pullback.fst P.A.hom x))
    (baseChange P x).isAb.proper hne (baseChange P x).isLB (pull_isLB hM _) hamp
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hN := LB.isLB_div hp P.isLB
  have hN' : ∀ {Y : Scheme.{0}} (f : Y ⟶ P.A.left), (LB.div (lbPow (M.pull f) a) (P.L.pull f)).IsLB := fun f =>
    LB.isLB_div (LB.isLB_linComb (pull_isLB hM f) _ _) (pull_isLB P.isLB f)
  obtain ⟨t, ht⟩ := exists_sec_ne_zero_of_lbIso (pull_isLB hN _) (hN' _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom x) a) ⟨s, hs⟩
  refine GlobalTheory.T.relAmple_of_ample_geometricFibres_abelianScheme hL S P M hM fun K' _ _ y => ?_
  obtain ⟨t', ht'⟩ := exists_sec_ne_zero_of_lbIso (hN' _) (pull_isLB hN _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom y) a).symm
    (GlobalTheory.T.exists_section_ne_zero_fibre_of_generic_section hL S P _ K K' x y t hN hx ht)
  obtain ⟨r, u, hu⟩ := GlobalTheory.T.exists_sections_cover_cube_effective_abelianVariety GlobalTheory.T.cube_theorem_and_sections_finite_growth_abelianVariety.1 K' (baseChange P y) _ t' (hN' _) ht'
  exact GlobalTheory.T.relAmple_of_cube_div_generated_field K' (baseChange P y).A (baseChange P y).L (M.pull (pullback.fst P.A.hom y)) a r u
    (baseChange P y).isAb.proper (baseChange P y).isLB (pull_isLB hM _) ha (baseChange P y).ample hu

end GlobalTheory.AmpleSpecialisation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsToricTorsionCubWeilOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_toric_torsion_cubWeil_one : Out.Laws3 → ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : RigLB G) (c : CubicalStr G L) (g N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), SmoothOfRelativeDimension g G.hom → (N : k) ≠ 0 → ∃ T : Set (Over.mk x ⟶ G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ y : Over.mk x ⟶ G, y ^ N = 1 → CubWeil c N τ y 1) ∧ Nat.card {p : Over.mk x ⟶ G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  intro h3 X G _ _ hG L c g N k _ _ x dG hN
  let G' : Over (Sp k) := (Over.pullback x).obj G
  have hp : IsGrpPullback G' G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback x G hG
  have := hG'.comm
  have := hG'.smooth
  have := hG'.geomConnected
  have dG' : SmoothOfRelativeDimension g G'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 dG
  obtain ⟨E⟩ := hG.fibres k x
  let := E.addCommGroup
  let := E.grpB
  have := E.free
  have := E.finite
  have := E.i_hom
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := h3.cubePull _ _ G G' (cubeMapOf hp) L c
  obtain ⟨σ⟩ := GlobalTheory.BiextTriv.main k E.X G' _ c' E.i E.i_hom
  have hw : pullback.fst G.hom x ≫ G.hom = G'.hom ≫ x := pullback.condition
  let U : Over (Sp k) := 𝟙_ (Over (Sp k))
  let ρ : Over.mk x ⟶ Over.mk (U.hom ≫ x) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk x ⟶ G) := (preHom ρ).comp (toBaseHom (toBase_mul_pullback G x) U)
  have hφ : ∀ a : U ⟶ G', (φ a).left = a.left ≫ pullback.fst G.hom x := fun a => Category.id_comp _
  have hb : Function.Bijective φ := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hφ, ← hφ, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm))
        (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  let e := MulEquiv.ofBijective φ hb
  have he : ∀ a : U ⟶ G', e a ^ N = 1 ↔ a ^ N = 1 := fun a => by rw [← map_pow, e.map_eq_one_iff]
  have hcount := GlobalTheory.card_torsion_mul_card_toric_torsion k G' E g N hG' dG' hN
  refine ⟨e '' {y | y ^ N = 1 ∧ ∃ t, y = t ≫ E.i}, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact (he a).2 ha
  · rintro _ ⟨_, ⟨ha, t, rfl⟩, rfl⟩ y hy
    obtain ⟨b, rfl⟩ := e.surjective y
    have ht : t ^ N = 1 := E.isKernel.hom_ext
      (by rw [MonObj.pow_comp, ha, MonObj.one_comp]) (toUnit_unique _ _)
    have h1 := σ.cubWeil ht ((he b).1 hy)
    have h2 := (GlobalTheory.UU.cubWeil_of_isPullCubical _ _ x G G' (cubeMapOf hp) hw (toBase_mul_pullback G x) L _ c c' hc' N U _ _ _ h1).comp ρ
    rw [map_one] at h2
    exact h2
  · rw [← hcount]
    congr 1
    · exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun a => (he a).symm)).symm
    · exact Nat.card_image_of_injective e.injective _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHeckeQuotientPointModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem heckePoints_of_laws :
    Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
        1 ≤ D.p + D.q → ToroidalHeckeCompatibility (H := H) (D := D) :=
  fun hL _ => heckePoints_of_parts_comm hL LiePull.lieMult_pull obj_pull ObjMaps.id_comp_cancel
    obj_isAbelianScheme_dim_rigidified_sym (moduli_rep_of_base ObjMaps.id_comp_cancel)
    (exists_tateIso_heckeQuotient SimAlg.sim_group) (exists_heckeQuotient_triple_of_laws hL)
    (weilIs_along_hom hL.globalFns) LieEtale.lieMult_iff_of_etale (lam_iso_of_weil_pairings hL)
    (exists_quotient_by_finite_group_of_points hL)

end GlobalTheory
end

