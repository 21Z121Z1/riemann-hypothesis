import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedPullbackConjugateTranslateEqTranslateL
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.InVVwIffOfNotTorsion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0656
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalAtOfUnif
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Degenerations.MemOfIsIntegralElem
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupPowValueEqOfConjugateTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaPowConj

theorem prod_telescope {U : Type} [CommGroup U] (F G : ℕ → U) (n : ℕ) :
    ∏ i ∈ Finset.range n, (F i * G i * (F (i + 1))⁻¹) = F 0 * (∏ i ∈ Finset.range n, G i) * (F n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
    group

theorem val_powGen_transport : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (N : ℕ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : ∀ i : ℕ, f ≫ (translT A (θ.pt ^ i)).left = (translT A' (θ'.pt ^ i)).left ≫ f) (hN : θ'.pt ^ N = 1) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (powGen A L k θ N) (q ≫ f) z J = val (powGen A' L' k θ' N) q z J' := by
  intro S S' A A' _ _ L L' T T' f k N θ θ' Ψ hT hN H Z q z J J' hJ hJ'
  rw [GlobalTheory.ConjPull.val_thetaPow θ N (q ≫ f) z hJ, GlobalTheory.ConjPull.val_thetaPow θ' N q z hJ']
  have step : ∀ i ∈ Finset.range N,
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        ((q ≫ f) ≫ (translT A (θ.pt ^ i)).left) z J =
      Ψ (q ≫ (translT A' (θ'.pt ^ i)).left) z J J' ^ k *
        val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ
          (q ≫ (translT A' (θ'.pt ^ i)).left) z J' *
        (Ψ (q ≫ (translT A' (θ'.pt ^ (i + 1))).left) z J J' ^ k)⁻¹ := by
    intro i _
    have e1 : (q ≫ f) ≫ (translT A (θ.pt ^ i)).left = (q ≫ (translT A' (θ'.pt ^ i)).left) ≫ f := by
      rw [Category.assoc, hT i, Category.assoc]
    have e2 : (q ≫ (translT A' (θ'.pt ^ i)).left) ≫ (translT A' θ'.pt).left =
        q ≫ (translT A' (θ'.pt ^ (i + 1))).left := by
      rw [Category.assoc, ← Over.comp_left, GlobalTheory.PullMove.translT_mul, pow_succ']
    rw [e1, H Z _ z J J' hJ hJ', e2]
  rw [Finset.prod_congr rfl step,
    prod_telescope (fun i => Ψ (q ≫ (translT A' (θ'.pt ^ i)).left) z J J' ^ k)
      (fun i => val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ
          (q ≫ (translT A' (θ'.pt ^ i)).left) z J')]
  simp only [hN, pow_zero]
  rw [mul_comm, ← _root_.mul_assoc, inv_mul_cancel, _root_.one_mul]

end GlobalTheory.ThetaPowConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetricLiftActionFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

namespace GlobalTheory.Mum.Desc

theorem isActOf_secExt : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (x : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → SymLift A.A A.L N N (baseEm em ≫ x) θ' → ∀ t t' : SecF A (Kb R) N, IsActOf A.A A.L N θ t t' → IsActOf A.A A.L N θ' (secExt A em N t) (secExt A em N t') := by
  intro R _ _ A F _ _ em N hN x θ θ' H H' t t' a
  exact GlobalTheory.WeightProbe.act_pull A hN (baseEm em) H H' a

end GlobalTheory.Mum.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetryValueEqOfConjugate
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaSymTransport

theorem val_symGen_eq : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (ν : LB.Gen (negLB A L k T)) (ν' : LB.Gen (negLB A' L' k T')) (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt⁻¹).left = (translT A' θ'.pt⁻¹).left ≫ f) (hneg : f ≫ (negT A T).left = (negT A' T').left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Hν : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (snd T' A' ≫ (GrpObj.inv : A' ⟶ A')).left]) (ε := ![k, -k]) ν' q z J' * (Ψ (q ≫ (negT A' T').left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (symGen A L k θ ν) (q ≫ f) z J = val (symGen A' L' k θ' ν') q z J' := by
  intro S S' A A' _ _ _ L L' T T' f k θ θ' ν ν' Ψ hT hneg H Hν Z q z J J' hJ hJ'
  have c₁ : (translT A' θ'.pt⁻¹).left ≫ (translT A' θ'.pt).left = 𝟙 _ := by
    rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, mul_inv_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]
  have c₂ : (negT A' T').left ≫ (translT A' θ'.pt).left = (translT A' θ'.pt⁻¹).left ≫ (negT A' T').left := by
    rw [← Over.comp_left, ← Over.comp_left, GlobalTheory.PullMove.negT_translT]
  have e₁ := H Z (q ≫ (translT A' θ'.pt⁻¹).left) z J J' hJ hJ'
  have e₂ := H Z (q ≫ (negT A' T').left) z J J' hJ hJ'
  have e₃ := Hν Z q z J J' hJ hJ'
  have e₄ := Hν Z (q ≫ (translT A' θ'.pt⁻¹).left) z J J' hJ hJ'
  simp only [Category.assoc, c₁, c₂, Category.comp_id, ← hT, ← hneg] at e₁ e₂ e₄
  rw [GlobalTheory.ConjPull.val_thetaSym _ _ _ _ hJ, GlobalTheory.ConjPull.val_thetaSym _ _ _ _ hJ']
  simp only [Category.assoc]
  rw [e₁, e₂, e₃, e₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

end GlobalTheory.ThetaSymTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyScalarIsUnitOnIntegralModels
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyUnitModels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

open GlobalTheory.FlagMod (ev_res ev_spMap le_preimage_mono)

theorem norm_bounds {κ : KeyRule} (hκ : IsKeyRule κ) (x : KeyIn ℂ) {τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c₀ : ℂ} (hab : GlobalTheory.KeyPow.charHalf _ a b) (hc : c₀ ≠ 0)
    (hN : GlobalTheory.KeyPow.NormalAt x τ Mx a b c₀) {C : ℝ} (hC : 0 < C) (h₁ : C⁻¹ ≤ ‖Mx.det‖ / ‖c₀‖ ^ 2)
    (h₂ : ‖Mx.det‖ / ‖c₀‖ ^ 2 ≤ C) : ‖(κ ℂ x : ℂ)‖ ≤ C ^ 4 ∧ ‖(κ ℂ x : ℂ)⁻¹‖ ≤ C ^ 4 := by
  have hr : 0 < ‖Mx.det‖ / ‖c₀‖ ^ 2 := (inv_pos.2 hC).trans_le h₁
  have hM : Mx.det ≠ 0 := fun h0 => by simp [h0] at hr
  obtain ⟨P, hg, rig, hrig, th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, hN₀, e₁, hMv⟩ := GlobalTheory.KeyConst.exists_rescale P hg rig hrig th hth v hv τ Mx _ _ c₀ hc hM hN
  obtain ⟨u, k₁, k₂, k₃, k₄, k₅, k₆⟩ := (GlobalTheory.KeyPow.normalAt_one_iff _ _ _ _).1 hN₀
  have e := hκ.1 ℂ P hg rig hrig _ hth₀ v₀ hv₀ th hth v hv c₀ Mx e₁ hMv
  rw [hκ.2.2.2.1 ⟨P, hg, rig, hrig, th₀, hth₀, v₀, hv₀⟩ u τ a b k₁ k₂ hab.1 hab.2 k₃ k₄ k₅ k₆, Units.val_one,
    _root_.mul_one] at e
  have q : 0 < ‖c₀‖ := norm_pos_iff.2 hc
  have e' : ‖(κ ℂ ⟨P, hg, rig, hrig, th, hth, v, hv⟩ : ℂ)‖ = (‖Mx.det‖ / ‖c₀‖ ^ 2) ^ 4 := by
    have := congrArg (‖·‖) e
    simp only [norm_mul, norm_pow] at this
    rw [div_pow, ← pow_mul, eq_div_iff (by positivity), ← this, _root_.mul_comm]
  constructor
  · rw [e']
    gcongr
  · rw [norm_inv, e', ← inv_pow]
    gcongr
    exact inv_le_of_inv_le₀ hC h₁

theorem countable_sections {X : Scheme.{0}} {O : Type} [CommRing O] [Countable O] (s : X ⟶ Sp O) [LocallyOfFiniteType s]
    {U : X.Opens} (hU : IsAffineOpen U) : Countable Γ(X, U) := by
  have hf : (s.appLE ⊤ _ le_top).hom.FiniteType :=
    (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨_, hU⟩ le_top)
  letI := (s.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp O, ⊤) Γ(X, U) := hf
  have hc : Countable Γ(Sp O, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.symm.injective.countable
  obtain ⟨n, f, hfs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  have : Countable (MvPolynomial (Fin n) Γ(Sp O, ⊤)) :=
    (MvPolynomial.basisMonomials (Fin n) Γ(Sp O, ⊤)).repr.injective.countable
  exact hfs.countable

theorem exists_chart_unit {W : ValuationSubring c.F} (Y : Model Xo c W.subtype) (hpq : 1 ≤ D.p + D.q)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule} (hκ : IsKeyRule κ)
    (M : GChart Y) : ∃ u : Γ(Y.X, M.U), IsUnit u ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X)
      (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), Set.range z ⊆ Set.range Y.j → KeyAt M z hz x → (κ K x : K) = ev z M.U hz u := by
  obtain ⟨⟨⟨_, hDed⟩, -, -⟩, hopen⟩ := GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W
  have := Y.jQ_open
  have hj : IsOpenImmersion Y.j := by unfold Model.j; infer_instance
  obtain ⟨-, -, -, -, -, hdom, -⟩ := GlobalTheory.genericPart_dense_proOpen W c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have hdense : Dense (Set.range Y.j) := hdom.denseRange
  obtain ⟨W₀, f₀, hW, hf⟩ := GlobalTheory.T.exists_unit_thetaKeyRule_open_model_chart E H D l Xo c _ _ Y inferInstance hj hpq κ hκ M
  have hcF : Countable c.F := by
    have := c.fin
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F
    rw [← Cardinal.mk_le_aleph0_iff]
    simpa [Cardinal.mkRat] using this
  have : Countable W := Subtype.val_injective.countable
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := M.dom
  have hpos : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h₁ := IsTotallyComplex.finrank E
    have h₂ : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact Nat.mul_pos (by omega) hpq
  have hWU : W₀ ≤ M.U := fun x hx => ((hW x).1 hx).1
  have hWj : ∀ {K : Type} [Field K] {z : Sp K ⟶ Y.X}, ⊤ ≤ z ⁻¹ᵁ W₀ → Set.range z ⊆ Set.range Y.j := fun hz => by
    rintro _ ⟨q, rfl⟩; exact ((hW _).1 (hz (Set.mem_univ q))).2
  have hne : ∃ x, x ∈ W₀ := by
    obtain ⟨q⟩ : Nonempty (Sp Γ(Y.X, M.U)) := inferInstanceAs (Nonempty (PrimeSpectrum _))
    obtain ⟨x, hx, hx'⟩ := hdense.exists_mem_open M.U.isOpen ⟨_, tau_le M.hU le_rfl (Set.mem_univ q)⟩
    exact ⟨x, (hW x).2 ⟨hx', hx⟩⟩
  obtain ⟨hinj, hext⟩ := GlobalTheory.GenExt.extend_of_integral_at_dvr _ _ W₀ hWU M.hU M.dom
    (IsLocallyNoetherian.component_noetherian ⟨_, M.hU⟩) (GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen M.hU)
    (countable_sections Y.s M.hU) hne
  have key : ∀ u : Γ(Y.X, W₀), (u = f₀.val ∨ u = (f₀⁻¹).val) → ∃ f, resG _ hWU f = u := by
    intro u hu
    refine hext u fun R K _ _ _ _ _ _ z hR hz h => ?_
    let y := IsOpenImmersion.lift Y.j (spMap (algebraMap R K) ≫ z) (hWj h)
    have : CharZero K := charZero_of_injective_ringHom (Spec.preimage (y ≫ pullback.snd _ _)).hom.injective
    refine GlobalTheory.T.integral_of_arcs_and_goodReduction_points E H D l Xo c W Y h3 h4 hs hj M.U W₀ u (fun x hx hx' => (hW x).2 ⟨hx, hx'⟩)
      (fun a χ hA hover hgen hχ => ?_) (fun R K _ _ _ _ _ _ _ z y hz hy hab h => ?_) R K z y hR hz
      (IsOpenImmersion.lift_fac _ _ _) h
    · obtain ⟨y, hy, T, C', hC', hT⟩ := GlobalTheory.ArcNormal.arc_normal_form _ _ _ _ _ _ _ Y hpq hP a χ hA hover hgen M hχ
      refine GlobalTheory.ArcReg.not_pole_of_bounded _ M.U W₀ u χ y M.hU hWU hχ hy ⟨T, C' ^ 4, fun w hw hyw => ?_⟩
      obtain ⟨x, -, hk⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M (y w) (le_preimage_mono hWU hyw) (hWj hyw) hpos
      obtain ⟨τ, Mx, a', b', c₀, k₁, k₂, k₃, k₄, k₅⟩ := hT w hw _ x hk
      obtain ⟨b₁, b₂⟩ := norm_bounds hκ x k₁ k₂ k₃ hC' k₄ k₅
      have e := hf ℂ (y w) hyw _ x hk
      rcases hu with rfl | rfl
      · rwa [e]
      · rwa [map_units_inv, e]
    · obtain ⟨x, -, hk⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M _ (le_preimage_comp _ hz) (hWj h) hpos
      obtain ⟨v, hv⟩ := GlobalTheory.T.isUnit_thetaKeyScalar_goodReduction_chart E H D l Xo c _ _ Y κ hκ M R K z hz y hy hab x hk
      have e := hf K _ h _ x hk
      rcases hu with rfl | rfl
      · exact ⟨v, by rw [e, hv]⟩
      · exact ⟨(v⁻¹ : Rˣ), by rw [map_units_inv, map_units_inv, e, hv]⟩
  obtain ⟨f, hf₁⟩ := key _ (Or.inl rfl)
  obtain ⟨f', hf₂⟩ := key _ (Or.inr rfl)
  refine ⟨f, IsUnit.of_mul_eq_one f' (hinj ?_), fun K _ _ z hz x hr hk => ?_⟩
  · exact ((RingHom.map_mul _ f f').trans ((congrArg₂ (· * ·) hf₁ hf₂).trans f₀.mul_inv)).trans (RingHom.map_one _).symm
  · have hz₀ : ⊤ ≤ z ⁻¹ᵁ W₀ := fun q hq => (hW _).2 ⟨hz hq, hr ⟨q, rfl⟩⟩
    rw [← hf K z hz₀ _ x hk, ← hf₁, ev_res z hWU hz₀ hz]

theorem lieComb_one {K : Type} [Field K] (x : KeyIn K) (i : Fin x.P.g) :
    IsLieComb ((1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i) x.v (x.v i) := by
  have : (1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i = Pi.single i 1 := by
    ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this]
  have := x.P.isAb.comm
  exact (GlobalTheory.LieComb.lieComb_algebra _ _ _ x.v x.basis.1).2.2.2.1 i

theorem unitAt_local {W : ValuationSubring c.F} (Y : Model Xo c W.subtype) (hpq : 1 ≤ D.p + D.q)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule} (hκ : IsKeyRule κ)
    (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] :
    UnitAt κ Y V K := by
  intro y yt hyt t m n w hw θ x hx
  obtain ⟨⟨⟨_, hDed⟩, -, -⟩, -⟩ := GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W
  obtain ⟨M, hM⟩ := GlobalTheory.FlagMod.exists_gChart hP (yt (IsLocalRing.closedPoint V))
  have hz : ⊤ ≤ yt ⁻¹ᵁ M.U := ((IsLocalRing.closed_point_mem_iff (U := yt ⁻¹ᵁ M.U)).1 hM).ge
  obtain ⟨u, hu, hval⟩ := exists_chart_unit Y hpq hP h3 h4 hs hκ M
  have := t.semi.smooth
  obtain ⟨θ₀, h₀⟩ : ∃ θ₀ : t.PP.L.Sec, NonzeroClosed (X := t.G) θ₀ := by
    obtain ⟨-, θ₀, -, -, hne⟩ := GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t yt m M.U hz M.θ M.θ_mem M.θ_ne
    obtain ⟨g, i, h₁, h₂⟩ := hne (IsLocalRing.closedPoint V)
    exact ⟨θ₀, g, h₁, TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩⟩
  have hC : ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) →
      Generates (X := t.G) θ → ∃ u : Vˣ, (κ K x : K) = algebraMap V K u := fun θ x hx hθ => by
    obtain ⟨x', a, d, hk, e⟩ := GlobalTheory.T.exists_generatingFrame_unit_change_to_chart E H D l Xo c _ _ Y M V K yt hz t m n w hw θ x hx hθ
    have e₁ := e κ hκ
    rw [hval K _ _ x' (by
      rw [hyt]; rintro _ ⟨q, rfl⟩; exact ⟨y q, (Scheme.Hom.comp_apply _ _ _).symm⟩) hk,
      ev_spMap (algebraMap V K) yt M.U hz, RingHom.comp_apply] at e₁
    refine ⟨(d ^ 4)⁻¹ * (a ^ 8 * (hu.map (ev yt M.U hz)).unit), ?_⟩
    have hd : algebraMap V K d ≠ 0 := (d.isUnit.map _).ne_zero
    rw [Units.val_mul, map_mul, map_units_inv, Units.val_mul, map_mul, IsUnit.unit_spec, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, map_pow, map_pow, e₁, inv_mul_cancel_left₀ (pow_ne_zero _ hd)]
  have hB : ∀ (θ : t.PP.L.Sec), Generates (X := t.G) θ → ∀ N : ℕ, Generates (X := pow t.G N) (boxSec t.G θ N) :=
    fun θ' hθ N => by
      obtain ⟨a, ha, -⟩ := hθ θ₀
      obtain ⟨hfl, g, hg, hnz⟩ := GlobalTheory.T.flat_fibrePower_and_externalTensorSection_nonzero_closedFibre V t.G t.PP.L θ' (NonzeroClosed.of_isMul ha h₀).2 N
      obtain ⟨X', p', φ, L', b, k₁, k₂, k₃, k₄⟩ := GlobalTheory.T.exists_line_sections_externalTensorPower_fibre V K _ t.G t.PP.L t.PP.rig θ n w x t.PP.isLB hx N
      exact generates_of_generic_line (pow t.G N).hom k₁ (LB.isLB_linComb t.PP.isLB _ _) k₂ k₃ b k₄ _ hg hnz
  refine ⟨fun hθ => ⟨hC θ x hx hθ, fun N _ => hB θ hθ N⟩, ?_⟩
  intro N hN σ a hσ hmul
  have hg₀ := generates_of_isFibreOf t.PP.isLB hx h₀
  obtain ⟨b, hθb, -⟩ := hg₀ θ
  obtain ⟨th₀, hth₀, hth, hx₀⟩ := GlobalTheory.T.exists_baseChange_rigidifiedSection_of_scalarMultiple V K _ t.G t.PP.L t.PP.rig θ n w x t.PP.isLB hx θ₀ b hθb
  obtain ⟨u₀, hu₀⟩ := hC θ₀ _ hx₀ hg₀
  have hbox₀ := hB θ₀ hg₀ N
  have hom := hκ.1 K x.P x.g_pos x.rig x.rig_gen th₀ hth₀ x.v x.basis x.th x.th_ne x.v x.basis (algebraMap V K b) 1
    hth (lieComb_one x)
  rw [Matrix.det_one, one_pow, _root_.one_mul] at hom
  obtain ⟨c', hc', -⟩ := hσ (boxSec t.G θ₀ N)
  have hcu : IsUnit c' := Generates.isUnit hσ hbox₀ hc'
  have ha : a = b ^ N * c' := (hσ (boxSec t.G θ N)).unique hmul (IsMul.trans (isMul_boxSec hθb N) hc')
  obtain ⟨k, rfl⟩ := hN
  refine ⟨hcu.unit * u₀ ^ k, ?_⟩
  rw [ha, Nat.mul_div_cancel_left k (by norm_num : 0 < 8)]
  simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [← hu₀, ← hom, pow_mul]
  ring

theorem unitAt_valuation {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (hpq : 1 ≤ D.p + D.q)
    (hβ : IsBaseRing β) (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule}
    (hκ : IsKeyRule κ) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [CharZero K] [Algebra V K]
    [IsFractionRing V K] : UnitAt κ Y V K := by
  intro y yt hyt t m
  have hinj := IsFractionRing.injective V K
  have sp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B),
      spMap f ≫ spMap g = spMap (f.comp g) := fun _ _ => (Spec.map_comp _ _).symm
  obtain ⟨io, hio⟩ : ∃ io : c.F →+* K, spMap io = y ≫ pullback.snd _ _ := ⟨_, Spec.map_preimage _⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : O →+* V, spMap b₀ = yt ≫ Y.s := ⟨_, Spec.map_preimage _⟩
  have hc : (algebraMap V K).comp b₀ = io.comp β := by
    have e : spMap ((algebraMap V K).comp b₀) = spMap (io.comp β) := by
      rw [← sp, ← sp, hb₀, hio, ← Category.assoc, hyt, Model.j, Category.assoc, Category.assoc, Category.assoc,
        pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  let W : ValuationSubring c.F :=
    { (algebraMap V K).range.comap io with
      mem_or_inv_mem' := fun a => by
        have := ValuationRing.isInteger_or_isInteger V (io a)
        rw [← map_inv₀] at this
        exact this }
  let b : O →+* W := β.codRestrict W.toSubring fun a => ⟨b₀ a, RingHom.congr_fun hc a⟩
  have hb : W.subtype.comp b = β := rfl
  let e := RingEquiv.ofBijective (algebraMap V K).rangeRestrict
    ⟨fun a a' h => hinj (congrArg Subtype.val h), (algebraMap V K).rangeRestrict_surjective⟩
  let b' : W →+* V := e.symm.toRingHom.comp ((io.comp W.subtype).codRestrict (algebraMap V K).range fun a => a.2)
  have hb' : b'.comp b = b₀ := RingHom.ext fun a => by
    apply e.injective
    exact (e.apply_symm_apply _).trans (Subtype.ext (RingHom.congr_fun hc a).symm)
  obtain ⟨_, _⟩ := GlobalTheory.T.isPreimmersion_flat_valuationSubring_baseRing E H l c O β hβ W b hb
  let yt' : Sp V ⟶ (locModel Y b hb).X := pullback.lift yt (spMap b') (by rw [sp, hb', hb₀])
  have hy' : yt' ≫ pullback.fst Y.s (spMap b) = yt := pullback.lift_fst _ _ _
  obtain ⟨m', -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := yt') (locMap Y b) (hy'.symm ▸ m)
  exact unitAt_local (locModel Y b hb) hpq (locModel_pushInvertible Y b hb (GlobalTheory.T.valuation_subring_dedekind_open_immersion E H l c W).1 hP) (localisedModel_uniformisation_baseChange Y b hb h3)
    (GlobalTheory.T.arcProperty_localisationBaseChange_of_model E H D l Xo c O β Y _ _ b hb h4) (GlobalTheory.T.splitFibres_localisedModel_baseChange E H D l Xo c O β Y _ _ b hb hs) hκ V K y yt' (by
      rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, Category.assoc, hy', locModel_j, hyt]) t m'

theorem keyUnitOnModels : KeyUnitOnModels := by
  intro κ hκ E _ _ _ H D l Xo c O _ β Y p h₁ h₂ _ h₄ h₅ h₆ h₇
  refine ⟨fun V K _ _ _ _ _ _ _ _ => unitAt_valuation Y h₁ h₂ h₄.2.2.1 h₅ h₆ h₇ hκ V K, fun V C _ _ _ _ _ _ _ hV => ?_⟩
  obtain ⟨_, _, _⟩ := GlobalTheory.GoodRedUnitBall.valuationRing_of_unitBall hV
  exact unitAt_valuation Y h₁ h₂ h₄.2.2.1 h₅ h₆ h₇ hκ V C

end GlobalTheory.KeyUnitModels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointConjAlgClosureAutomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoint_conj_algClosure_automorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (k : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (I : Type) (x x' : I → (TFK (R := R) (Kb R) ⟶ A.A)) (v : I → Kb R), (∀ i, (x' i).left = spMap σ.toRingHom ≫ (x i).left) → IsThetaPt A k x (fun i => GlobalTheory.Ex.fnOf (v i)) → IsThetaPt A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
  first | exact @GlobalTheory.isThetaPt_conj | exact GlobalTheory.isThetaPt_conj | (intros; apply GlobalTheory.isThetaPt_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionCrossRelationIffOfThetaActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSectionCrossRelation_iff_of_thetaAction : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j j' : ℕ) (θ : ThetaGrp A₂.A A₂.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A₁.A A₁.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ c → ∀ (t₁ t₂ T₁ T₂ : SecA A₂ F j) (t₁' t₂' T₁' T₂' : SecA A₁ F j'), IsActOf A₂.A A₂.L j θ t₁ T₁ → IsActOf A₂.A A₂.L j θ t₂ T₂ → IsActOf A₁.A A₁.L j' θ' t₁' T₁' → IsActOf A₁.A A₁.L j' θ' t₂' T₂' → (CrossH c t₁ t₂ t₁' t₂' ↔ CrossH c T₁ T₂ T₁' T₂') := by
  first | exact @GlobalTheory.crossH_iff_of_isActOf | exact GlobalTheory.crossH_iff_of_isActOf | (intros; apply GlobalTheory.crossH_iff_of_isActOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesValuesGaloisScalar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.values_galois_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ m : ℕ, Odd m → IsUnit (m : R) → ∀ v : QkPt D.toPre (Kb R) (m ^ 2) → Kb R, (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) (m ^ 2) → QkPt D.toPre C (m ^ 2)) (q : QkPt D.toPre (Kb R) (m ^ 2) → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i)) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) (m ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p' := by
  intro R _ _ _ hR D A lab hT m hm hmu v H σ
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em₀, hW, hφ, hloc, -, -, -, -⟩ := hT
  obtain ⟨C, _, _, _, _, _, _, hC⟩ := GlobalTheory.Ex.StepInh.exists_cExt W hW
  have hg : Function.Injective ((algebraMap (FractionRing W) C).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) C).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) C := (IsFractionRing.lift hg).toAlgebra
  have hA : ∀ r : R, algebraMap (FractionRing R) C (algebraMap R _ r) =
      algebraMap (FractionRing W) C (algebraMap W _ (φ r)) := fun r => IsFractionRing.lift_algebraMap hg r
  haveI := hloc
  have hCR : GlobalTheory.Ex.CExt R (maximalIdeal R) C :=
    ⟨fun r => by rw [hA]; exact hC.1 _, fun r hr => by rw [hA]; exact hC.2 _ (map_nonunit φ r hr)⟩
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, nu, -⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.firstFiveLaws.1 R D.toPre D.psi_even D.tau_bimult C ⊤
    (fun _ => trivial)
  have hB := D.tau_bimult
  let em : Kb R →ₐ[FractionRing R] C := IsAlgClosed.lift
  have hq := ((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult C N nu).2.2.2.2 (m ^ 2)).1
  choose e₁ he₁ using fun i => GlobalTheory.LabTrans.exists_ext hB em i
  choose e₂ he₂ using fun i => GlobalTheory.LabTrans.exists_ext hB σ i
  choose qq hqq using fun x : QkPt D.toPre C (m ^ 2) => (hq x).exists
  obtain ⟨s, hs⟩ := H C hCR em N nu e₁ (fun i => qq (e₁ i)) he₁ (fun i => hqq _)
  obtain ⟨s', hs'⟩ := H C hCR (em.comp σ) N nu (fun i => e₁ (e₂ i)) (fun i => qq (e₁ (e₂ i)))
    (fun i => GlobalTheory.LabTrans.qkExt_trans (he₂ i) (he₁ (e₂ i))) (fun i => hqq _)
  have key : ∀ p p', QkExt σ.toRingHom p p' → em (σ (v p)) = ((s' * s⁻¹ : Cˣ) : C) * em (v p') := by
    intro p p' h
    obtain rfl : e₂ p = p' := GlobalTheory.LabTrans.ext_unique hB σ (he₂ p) h
    have h1 := hs' p
    have h2 := hs (e₂ p)
    rw [AlgHom.comp_apply] at h1
    rw [h1, h2, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left]
  have emi : Function.Injective em := em.toRingHom.injective
  by_cases hex : ∃ p p', QkExt σ.toRingHom p p' ∧ v p' ≠ 0
  · obtain ⟨p₀, p₀', h₀, hv₀⟩ := hex
    have hσ0 : σ (v p₀) ≠ 0 := by
      intro h0
      have k0 := key p₀ p₀' h₀
      rw [h0, map_zero] at k0
      exact hv₀ ((map_eq_zero em).1 ((mul_eq_zero.1 k0.symm).resolve_left (Units.ne_zero _)))
    refine ⟨Units.mk0 (σ (v p₀) / v p₀') (div_ne_zero hσ0 hv₀), fun p p' h => emi ?_⟩
    have hne : em (v p₀') ≠ 0 := (map_ne_zero em).2 hv₀
    rw [Units.val_mk0, map_mul, map_div₀, key p p' h, key p₀ p₀' h₀]
    field_simp
  · push_neg at hex
    refine ⟨1, fun p p' h => ?_⟩
    have k := key p p' h
    rw [hex p p' h, map_zero, mul_zero] at k
    rw [hex p p' h, mul_zero]
    exact (map_eq_zero em).1 k
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTowerSameGenericFibreRealisations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem Tower.same : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ 𝔗 : Tower X₁ act, GlobalTheory.Poinc.Same X₁.ρ act 𝔗.X₂.ρ 𝔗.act₂ 𝔗.lam (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁) := by
  intro g n F W Z i X₁ act hact 𝔗
  let f₂ : Sp 𝔗.X₂.Ω₁ ⟶ Sp 𝔗.X₂.S.R := spMap 𝔗.X₂.S.R.val.toRingHom
  let P₀ := GlobalTheory.StrictPull.polPull 𝔗.X₂.ρ.P f₂
  let a' : P₀.A.left ⟶ 𝔗.X₂.ρ.P.A.left := pullback.fst 𝔗.X₂.ρ.P.A.hom f₂
  have hring : (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om := by
    ext x; exact (𝔗.om_eq x).symm
  have hsp : spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) = f₂ ≫ spMap 𝔗.om := by
    rw [hring]; exact Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔗.X₂.S.R.val.toRingHom)
  have ha' : IsGrpPullback P₀.A 𝔗.X₂.ρ.P.A f₂ a' := isGrpPullback_pullback _ _
  have hr : LBIso P₀.L (𝔗.X₂.ρ.P.L.pull a') := ⟨idIso _, idIso_isGen P₀.isLB⟩
  refine ⟨P₀, a' ≫ 𝔗.φ, a', fun E => (Over.pullback f₂).map (𝔗.act₂ E), ?_, ha', ?_, hr, ?_, ?_⟩
  · exact (ha'.comp 𝔗.cart).congr hsp.symm rfl
  · exact LBIso.trans P₀.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hr (lbIso_pull_comp 𝔗.lb a')
  · intro E
    have h1 : ((Over.pullback f₂).map (𝔗.act₂ E)).left ≫ a' = a' ≫ (𝔗.act₂ E).left :=
      pullback.lift_fst _ _ _
    refine ⟨?_, h1⟩
    have h2 : (a' ≫ (𝔗.act₂ E).left) ≫ 𝔗.φ = a' ≫ 𝔗.φ ≫ (act E).left := by
      rw [Category.assoc, 𝔗.act_eq]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) h1).trans h2)
  · intro x
    have hc : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ ≫ f₂ := by
      rw [Category.assoc, Over.w (𝔗.X₂.ρ.pt (𝔗.lam x))]
      simp [baseOver]
    refine ⟨pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc, ?_, ?_⟩
    · have hw : pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc ≫ a' = f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left :=
        pullback.lift_fst _ _ _
      have h3 : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.φ =
          spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) ≫ (X₁.ρ.pt x).left := by
        rw [Category.assoc, 𝔗.lam_pt, hsp, Category.assoc]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) hw).trans h3)
    · exact pullback.lift_fst _ _ _
end GlobalTheory.Poinc.Sep
end
end

