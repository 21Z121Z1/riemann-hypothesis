import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0376
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0353
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0360
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatValEqValAt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.HtModel

theorem ratVal_eq_valAt {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k} {σ : k →+* ℂ}
    (f : Z.functionField) (y : CxPts q σ) : ratVal f y = valAt y.1 f := by
  by_cases h : RegAt (under y) f
  · obtain ⟨U, hU, a, rfl⟩ := h.exists_fnOf
    have hy : y ∈ CxPts.ptsIn q σ U := CxPts.mem_ptsIn.2 hU
    rw [ratVal_fnOf hy, OfModel.valAt_fnOf y.1 hU hy, CxPts.ev_eq hy]
    rfl
  · rw [ratVal, dif_neg h, valAt, dif_neg h]

theorem bijective_comp (F : Type) [Field F] [NumberField F] :
    Function.Bijective fun σ : F →+* ℂ => σ.comp (algebraMap (𝓞 F) F) := by
  refine ⟨fun σ τ h => ?_, fun σ => ?_⟩
  · exact IsFractionRing.ringHom_ext (A := 𝓞 F) fun a => RingHom.congr_fun h a
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (I := RingHom.ker σ) (eq_bot_iff.2 fun n hn => ?_)
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hn
    exact Int.cast_eq_zero.1 hn
  refine ⟨IsFractionRing.lift (A := 𝓞 F) (K := F) hσ, RingHom.ext fun a => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

open Classical in

theorem ht_eq : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+), A.Induced M L k 0 → ∀ (x : Y.X) (a : ℝ), IsClosed ({x} : Set Y.X) → ArInt.IsPtHt L (M.j x) a → A.ht x = a / (((k : ℕ) : ℝ) * (A.n : ℕ)) := by
  intro F _ _ C Y A M L k ⟨_, r, hr, hinf, hfin⟩ x a hx ⟨h, H, ha⟩
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (M.j x)
  have := M.ar.isNoetherian_sub i
  obtain ⟨hc, hd⟩ := GlobalTheory.T.closed_point_algebraic F Y M x hx
  have hri : Set.range i = closure {M.j x} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hri] at hd
  rw [← hi] at hc
  have hc' : CharZero (Z.residueField (genericPoint Z)) :=
    charZero_of_injective_ringHom (i.residueFieldMap (genericPoint Z)).hom.injective
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ M.p) 0 := M.ar.of_isClosedImmersion i hcΓ hd
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  have : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip this
  have he : A.D.IsEqn x (eqn A.D x) := (A.D.exists_isEqn x).choose_spec
  have hu (c) (hc : x ∈ (L.B.pull M.j).U c) :
      UnitAt x (((eqn A.D x)⁻¹ ^ (k : ℕ) * r c : Y.Fnˣ) : Y.Fn) := by
    have := (he.nsmul k).iff_unitAt.1 (hr.isEqn c x hc)
    rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this
  obtain ⟨s, hs, hval⟩ := GlobalTheory.T.rational_section_extension M.X Y.X Z M.j i x hi L.B L.isLB r hr.isRatSec _ hu
  have hdeg := H.point Z i hcΓ hd s hs
  have hne := (ExtConj.main F).1

  obtain ⟨E, hE⟩ := GlobalTheory.T.generic_points_equiv_fibre F Y M x Z i hZ hi (AlgebraicClosure F) (algebraMap F _)
  have h₁ := GlobalTheory.T.local_equations_height_sum F Z (i ≫ M.p) hZ ((L.restr i).div hs) (fun v => (hne v).some)
    (fun v y => (k : ℕ) * A.lg v (hne v).some (E y).1) (fun v y yt hyt => by
      obtain ⟨c, hc⟩ := exists_chart L.isLB (i (yt (IsLocalRing.closedPoint _)))
      have hU : ⊤ ≤ (yt ≫ i) ⁻¹ᵁ L.B.U c := (Scheme.preimage_eq_top_of_closedPoint_mem (yt ≫ i) hc).ge
      have e₁ : spMap (hne v).some.O.subtype ≫ yt ≫ i = (E y).1.1 ≫ M.j := by
        rw [← Category.assoc, hyt, (hE y).1]
      refine ⟨s fun _ => c, (presents_divOfRatSec _ hs).isEqn _ _ (Set.mem_iInter.2 fun _ => hc), ?_⟩
      have hxc : M.j x ∈ L.B.U c := by
        have := Set.mem_iInter.1 (OfModel.le_chart M L.B _ (E y).1 (yt ≫ i) e₁ (i := fun _ => c) hU
          (x := IsLocalRing.closedPoint _) trivial) PUnit.unit
        rw [← (E y).2]
        exact this
      rw [hfin v _ (E y).1 (yt ≫ i) (fun _ => c) e₁ hU, hval _ _ _ c (hE y).1 (E y).2 (hE y).2 hxc, (E y).2]
      simp)
  have h₂ (v) : ∑ᶠ y, ((k : ℕ) : ℝ) * A.lg v (hne v).some (E y).1 =
      (k : ℕ) * if h : Nonempty (Ext v) then ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v h.some y else 0 := by
    rw [dif_pos (hne v), ← mul_finsum, ← finsum_subtype_eq_finsum_cond]
    exact congrArg _ (finsum_comp_equiv E (f := fun y => A.lg v (hne v).some y.1))
  replace h₁ := h₁.trans (congrArg (- ·) (finsum_congr h₂))

  have h₃ (σ : F →+* ℂ) : ∑ᶠ y : CxPts (i ≫ M.p) (σ.comp (algebraMap (𝓞 F) F)), logNorm ((L.restr i).φ _) s y =
      (k : ℕ) * ∑ᶠ (z : Pts Y σ) (_ : under z = x),
        (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z) / 2 -
          (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) := by
    obtain ⟨E, hE⟩ := GlobalTheory.T.generic_points_equiv_fibre F Y M x Z i hZ hi ℂ σ
    rw [← finsum_subtype_eq_finsum_cond, mul_finsum]
    refine finsum_eq_of_bijective E E.bijective fun y => ?_
    have hp := CxPts.mem_ptsIn.1 (CxPts.mem_pick ((L.restr i).φ (σ.comp (algebraMap (𝓞 F) F))).isLB y)
    unfold logNorm
    generalize CxPts.pick ((L.restr i).φ (σ.comp (algebraMap (𝓞 F) F))).isLB y = c at hp ⊢
    have hxc : M.j x ∈ L.B.U (c PUnit.unit) := by
      have := Set.mem_iInter.1 hp PUnit.unit
      rw [← hi, ← (hE y).2]
      exact this
    have hx' : under (E y).1 = x := (E y).2
    have hxc' : x ∈ (L.B.pull M.j).U c := Set.mem_iInter.2 fun _ => hxc
    have hg : A.D.GeneratesAt (under (E y).1) ((eqn A.D x)⁻¹ : Y.Fnˣ) := by
      rw [hx', Units.val_inv_eq_inv_val]
      exact CartierDiv.isEqn_iff_generatesAt_inv.1 he
    have hreg : ((k : ℕ) • A.D).RegularAt (under (E y).1) ((((eqn A.D x)⁻¹ : Y.Fnˣ) : Y.Fn) ^ (k : ℕ)) := by
      rw [hx', ← Units.val_pow_eq_pow_val, inv_pow, Units.val_inv_eq_inv_val]
      exact (CartierDiv.isEqn_iff_generatesAt_inv.1 (he.nsmul k)).regularAt
    have e₁ := hinf σ (E y).1 (Points.PtsOver.map i rfl _ y) c _ (hE y).1.symm (hx'.symm ▸ hxc') hreg
    rw [C.pn_mPow _ _ _ _ _ _ _ hg, ← Units.val_pow_eq_pow_val, ← Units.val_mul] at e₁
    have h0 : ‖ratVal (((eqn A.D x)⁻¹ ^ (k : ℕ) * r c : Y.Fnˣ) : Y.Fn) (E y).1‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (by rw [hx']; exact hu c hxc'))
    have e₂ := congrArg Real.log e₁
    have h0' : C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) (E y).1 ^ (k : ℕ) ≠ 0 :=
      right_ne_zero_of_mul (e₁.trans_ne (mul_ne_zero (pow_ne_zero _ h0) (Real.exp_ne_zero _)))
    rw [Real.log_mul (Real.exp_ne_zero _) h0', Real.log_mul (pow_ne_zero _ h0) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp, Real.log_pow, Real.log_pow, ratVal_eq_valAt] at e₂
    have e₃ := hval ℂ _ _ (c PUnit.unit) (hE y).1 (E y).2 (hE y).2 hxc
    have e₄ := (L.φ _).pull_φ i rfl c y
    rw [ratVal_eq_valAt]
    refine (congrArg₂ (fun a b => Real.log ‖a‖ - b / 2) e₃ e₄).trans ?_
    push_cast at e₂
    change Real.log ‖valAt (E y).1.1 (((eqn A.D x)⁻¹ ^ (k : ℕ) * r c : Y.Fnˣ) : Y.Fn)‖ - _ = _
    push_cast
    linarith
  unfold HermLB.curveDeg at hdeg
  rw [h₁, ← finsum_eq_of_bijective _ (bijective_comp F) fun σ => (h₃ σ).symm, hi, ha,
    GlobalTheory.T.residue_embeddings_card F Y M x hx, ← mul_finsum, ← mul_finsum, finsum_eq_sum_of_fintype (α := F →+* ℂ)] at hdeg
  obtain ⟨_, _⟩ := ExtConj.pts Y x hx
  have hN : (Nat.card {y : AlgPt Y // below y.1 = x} : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hk : ((k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 A.n.ne_zero
  rw [Adl.ht, div_eq_div_iff (by positivity) (by positivity)]
  rw [Nat.cast_mul] at hdeg
  linear_combination (-((A.n : ℕ) : ℝ)) * hdeg

end GlobalTheory.TrueGeo.HtModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpan
section
set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

variable {ι : Type} [Fintype ι] {m : ι → ℕ}

theorem charpolyRev_neg_lie_nsum (ρ : PolyRep m) (k : ℕ) {S : Type} [CommRing S] (A : Mat m S) :
    Matrix.charpolyRev (-((ρ.nsum k).lie A)) = (Matrix.charpolyRev (-(ρ.lie A))) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, Matrix.charpolyRev]
    haveI : IsEmpty (Fin (ρ.nsum 0).M) := inferInstanceAs (IsEmpty (Fin 0))
    exact Matrix.det_isEmpty
  | succ k ih =>
    rw [pow_succ, ← ih, ← GlobalTheory.T.charpolyRev_neg_finSumBlockDiagonalMatrix]
    exact congrArg (fun L => Matrix.charpolyRev (-L)) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_directSum (ρ.nsum k) ρ A)

theorem chern_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (ρ : PolyRep m) :
    (fun A : Mat m S => (Matrix.charpolyRev (-(ρ.lie A))).coeff n) ∈ Reach m n S :=
  Submodule.subset_span ⟨ρ, rfl⟩

theorem ptr_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (ρ : PolyRep m) :
    (fun A : Mat m S => ρ.ptr n A) ∈ Reach m n S := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := (Reach m 0 S).smul_mem (ρ.M : ℝ) (chern_mem_reach 0 S ρ)
    convert h using 1
    funext A
    have h0 : (Matrix.charpolyRev (-(ρ.lie A))).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    simp [PolyRep.ptr, h0, Algebra.smul_def]
  · obtain ⟨c, hc⟩ := GlobalTheory.T.exists_trace_pow_eq_sum_smul_coeff_charpolyRev n hn
    have h := (Reach m n S).sum_mem (t := Finset.range (n + 1))
      (fun k _ => (Reach m n S).smul_mem (c k) (chern_mem_reach n S (ρ.nsum k)))
    convert h using 1
    funext A
    rw [Finset.sum_apply, PolyRep.ptr, ← hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, charpolyRev_neg_lie_nsum]

theorem ptr_tensor (ρ σ : PolyRep m) (N : ℕ) {S : Type} [CommRing S] (A : Mat m S) :
    (ρ.tensor σ).ptr N A =
      ∑ a ∈ Finset.range (N + 1), (N.choose a : S) * ρ.ptr a A * σ.ptr (N - a) A := by
  simp only [PolyRep.ptr]
  rw [← GlobalTheory.T.trace_pow_finProdKronecker_add_binomial]
  exact congrArg (fun L => (L ^ N).trace) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_tensorProduct ρ σ A)

theorem ptr_mul_trProd_mem_reach (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (l : List (ι × ℕ)) :
    (∀ x ∈ l, 1 ≤ x.2) → ∀ r : ℕ, r + (l.map Prod.snd).sum = n → ∀ ρ : PolyRep m,
      (fun A : Mat m S => ρ.ptr r A * trProd l A) ∈ Reach m n S := by
  induction l with
  | nil =>
    intro _ r hr ρ
    have hr' : r = n := by simpa using hr
    subst hr'
    simpa [trProd] using ptr_mem_reach r S ρ
  | cons x l ih =>
    obtain ⟨τ, i⟩ := x
    intro hl r hr ρ
    have hi : 1 ≤ i := hl (τ, i) (by simp)
    have hr' : (r + i) + (l.map Prod.snd).sum = n := by
      simp only [List.map_cons, List.sum_cons] at hr
      omega
    obtain ⟨J, _, σ, c, hσ⟩ := GlobalTheory.T.exists_polyRep_combination_pure_power_trace m n S τ i hi
    have ih' := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (r + i) hr'
    have h := (Reach m n S).smul_mem (((r + i).choose r : ℝ)⁻¹)
      ((Reach m n S).sum_mem (t := Finset.univ)
        (fun j _ => (Reach m n S).smul_mem (c j) (ih' (ρ.tensor (σ j)))))
    convert h using 1
    funext A
    have hne : (((r + i).choose r : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_right r i)).ne'
    have key : ∑ j, c j • (ρ.tensor (σ j)).ptr (r + i) A =
        (((r + i).choose r : ℕ) : ℝ) • (ρ.ptr r A * ((A τ) ^ i).trace) := by
      simp only [ptr_tensor, Finset.smul_sum]
      rw [Finset.sum_comm]
      have e : ∀ a ∈ Finset.range (r + i + 1),
          ∑ j, c j • ((((r + i).choose a : ℕ) : S) * ρ.ptr a A * (σ j).ptr (r + i - a) A) =
            (((r + i).choose a : ℕ) : S) * ρ.ptr a A *
              (if r + i - a = i then ((A τ) ^ i).trace else 0) := by
        intro a _
        rw [← hσ A (r + i - a) (by omega), Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm
      rw [Finset.sum_congr rfl e, Finset.sum_eq_single r]
      · rw [if_pos (by omega), Algebra.smul_def, map_natCast, mul_assoc]
      · intro a ha har
        rw [Finset.mem_range] at ha
        rw [if_neg (by omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    simp only [Pi.smul_apply, Finset.sum_apply]
    have e2 : ∑ j, c j • ((ρ.tensor (σ j)).ptr (r + i) A * trProd l A) =
        (∑ j, c j • (ρ.tensor (σ j)).ptr (r + i) A) * trProd l A := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => (smul_mul_assoc _ _ _).symm
    rw [e2, key, smul_mul_assoc, smul_smul, inv_mul_cancel₀ hne, one_smul]
    simp only [trProd, List.map_cons, List.prod_cons, mul_assoc]

theorem trProd_mem_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (l : List (ι × ℕ)) (hl : ∀ x ∈ l, 1 ≤ x.2) (hs : (l.map Prod.snd).sum = n) :
    (fun A : Mat m S => trProd l A) ∈ Reach m n S := by
  have h := ptr_mul_trProd_mem_reach n S l hl 0 (by simpa using hs) (PolyRep.triv m)
  convert h using 2 with A
  have : (PolyRep.triv m).ptr 0 A = 1 := by
    rw [PolyRep.ptr, pow_zero, Matrix.trace_one, Fintype.card_fin]
    exact Nat.cast_one
  rw [this, one_mul]

end GlobalTheory.GoodMetric.ChernSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalCharacterAdmissibleConductorInertiaSurjStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_surjective_of_admQ : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (hE : IsEmpty D.nd.Loc) (F : TwF T)
    (i : T.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ (T.ntw hE F (TwL.empty T)) i Q M →
    ∀ P (hP : P ∈ Q),
      (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := D.host.E) A =>
          Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩) ∧
      ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' →
        ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩ = 0 := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.universalCharacter_admissibleConductor_inertia_surjective | exact GlobalTheory.HeightCounting.FormsStep.universalCharacter_admissibleConductor_inertia_surjective | (intros; apply GlobalTheory.HeightCounting.FormsStep.universalCharacter_admissibleConductor_inertia_surjective <;> assumption)
end

