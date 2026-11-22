import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0127
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0129
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTie
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ContentZeroAtSmallPrimes
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0128
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0130

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartValuesBoundProductsOnPlanesStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartValues_bound_products_on_planes : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) [Fintype Orb] (I0 : Orb → Type) [∀ o, Fintype (I0 o)] (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V) (Ls : LetSys C dd) (N n : ℕ) (pl : Fin N × Fin 2 ↪ Fin n) (ν : ℝ), SelfSep Y p → (ν : EReal) ≤ Y.nuPlE Ls n → RF.ValO (fun o => (Y.rawSelf (p o)).rowData (H o)) N (imgFamS Y p Ls pl) ν := by
  first | exact @GlobalTheory.RowAt.valO_self | exact GlobalTheory.RowAt.valO_self | (intros; apply GlobalTheory.RowAt.valO_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudSizesBetweenZeroAndTwiceBStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cloudSizes_between_zero_and_twice_b : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → L.Sc + L.etaSz ≤ 2 * L.sc.b ∧ ∀ j, InR D j → (∀ τ, 0 ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b) ∧ (∀ t, wj D j (plOf D (false, t)) ≤ 2 * L.sc.b') ∧ ∀ z, (numOf D L).w j z = wj D j (plOf D z) := by
  first | exact @GlobalTheory.RunDepth.sizes_le_two_mul | exact GlobalTheory.RunDepth.sizes_le_two_mul | (intros; apply GlobalTheory.RunDepth.sizes_le_two_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEmbeddingsIntegralAndDistinctModMaximalStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmEmbeddings_integral_and_distinct_mod_maximal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → (∀ τ x, V.Ge 0 (emA3 io ι τ x)) ∧ ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a : 𝓞 E, V.v (emA3 io ι τ a - emA3 io ι τ' a) = 0 := by
  first | exact @GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' | exact GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' | (intros; apply GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeDirectionsEigenbasisValuedIntegersStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTypeDirections_eigenbasis_valuedIntegers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → ∀ τ : E →+* ℂ, IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO τ) (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j)) ∧ Function.Surjective (res (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j))) := by
  first | exact @GlobalTheory.CharDepth.isEigBasis_valExt | exact GlobalTheory.CharDepth.isEigBasis_valExt | (intros; apply GlobalTheory.CharDepth.isEigBasis_valExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeFrobeniusOrbitsLabelAtSplitPrime
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.LabSplit

theorem exists_reps {P : Type} [Fintype P] (d : ℕ) [NeZero d] (pos : P → ℕ → P) (h0 : ∀ z, pos z 0 = z)
    (hadd : ∀ z s t, pos (pos z s) t = pos z (s + t)) (hfree : ∀ z s t, pos z s = pos z t ↔ s ≡ t [MOD d]) :
    ∃ Z : Finset P, ∀ z', ∃! p : P × ZMod d, p.1 ∈ Z ∧ pos p.1 p.2.val = z' := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  let S : Setoid P :=
    { r := fun z z' => ∃ s, pos z s = z'
      iseqv :=
        { refl := fun z => ⟨0, h0 z⟩
          symm := by
            rintro z _ ⟨s, rfl⟩
            refine ⟨(d - 1) * s, ?_⟩
            rw [hadd]
            conv_rhs => rw [← h0 z]
            rw [hfree]
            have : s + (d - 1) * s = d * s := by
              obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
              simp only [Nat.add_sub_cancel_left]; ring
            rw [this]
            exact (Nat.modEq_zero_iff_dvd).2 (dvd_mul_right _ _)
          trans := by
            rintro z _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
            exact ⟨s + t, (hadd z s t).symm⟩ } }
  refine ⟨Finset.univ.filter fun z => (Quotient.mk S z).out = z, fun z' => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s, pos (Quotient.mk S z').out s = z' := Quotient.mk_out (s := S) z'
  have hmod : ((s : ZMod d)).val ≡ s [MOD d] := by
    rw [ZMod.val_natCast]; exact Nat.mod_modEq s d
  refine ⟨((Quotient.mk S z').out, (s : ZMod d)), ⟨by simp, ?_⟩, ?_⟩
  · exact ((hfree _ _ _).2 hmod).trans hs
  · rintro ⟨z, t⟩ ⟨hz, ht⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ht
    have h1 : Quotient.mk S z = Quotient.mk S z' := Quotient.sound ⟨_, ht⟩
    have h2 : z = (Quotient.mk S z').out := by rw [← h1, hz]
    refine Prod.ext h2 ?_
    rw [h2, ← hs] at ht
    have h3 : pos (Quotient.mk S z').out t.val = pos (Quotient.mk S z').out s := by
      rw [hs] at ht ⊢; exact ht
    have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).2 ((hfree _ _ _).1 h3)
    simpa using h4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)

theorem rt_sq_field : (H.rt : E) ^ 2 = -(H.d : E) := by
  have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  simpa using this

theorem inPsi_conj_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, rt_sq_field]; simp
  have h2 : starRingEnd ℂ H.rt0 = -H.rt0 := by
    have h := H.sqrt_neg_disc_sq
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [pow_two] at hre him
    have : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
    apply Complex.ext <;> simp [this]
  have h0 : -H.rt0 ≠ H.rt0 := by
    intro h
    have h3 : H.rt0 = 0 := by linear_combination -h / 2
    have h4 := H.sqrt_neg_disc_sq
    rw [h3] at h4
    have : (H.d : ℂ) = 0 := by linear_combination h4
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · rw [h, h2]; simp [h0]
  · rw [h, map_neg, h2]; simp [h0]

theorem not_MM_neg_sub_pow {C : Type} [Field C] (V : VF C) (d : ℕ) (r : C) (hr : r ^ 2 = -(d : C)) (hi : V.Ge 0 r)
    (h2 : V.l ≠ 2) (hj : jacobiSym (-(d : ℤ)) V.l = 1) : ¬ V.MM (-r - r ^ V.l) := by
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
  have hp := legendreSym.eq_pow V.l (-(d : ℤ))
  rw [hj] at hp
  have hdv : (V.l : ℤ) ∣ (-(d : ℤ)) ^ (V.l / 2) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hp ⊢
    rw [← hp, sub_self]
  obtain ⟨k, hk⟩ := hdv
  have hnd : ¬ (V.l : ℤ) ∣ -(d : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← legendreSym.eq_zero_iff, hj]
    exact one_ne_zero
  have hpr : Prime (V.l : ℤ) := Nat.prime_iff_prime_int.1 V.l_prime
  have hn2 : ¬ (V.l : ℤ) ∣ (2 : ℤ) := by
    intro h
    have : V.l ∣ 2 := by exact_mod_cast h
    exact h2 ((Nat.prime_dvd_prime_iff_eq V.l_prime Nat.prime_two).1 this)
  have hv2 := GlobalTheory.EmbSep.v_intCast_eq_zero V hn2
  have hvd := GlobalTheory.EmbSep.v_intCast_eq_zero V hnd
  have hodd : V.l = 2 * (V.l / 2) + 1 := by
    have := V.l_prime.eq_two_or_odd.resolve_left h2
    omega
  have hkC : (-(d : C)) ^ (V.l / 2) = 1 + (V.l : C) * (k : C) := by
    have := congrArg (Int.cast : ℤ → C) hk
    push_cast at this
    linear_combination this
  have hpow : r ^ V.l = r + (V.l : C) * ((k : C) * r) := by
    conv_lhs => rw [hodd, pow_succ, pow_mul, hr, hkC]
    ring
  have hk0 : V.Ge 0 (k : C) := by
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · simpa using VF.ge_natCast (V := V) n
    · simpa using (VF.ge_natCast (V := V) n).neg
  intro hM
  have h1 : 0 < V.v ((V.l : C) * ((k : C) * r)) := by
    rw [V.v.map_mul, V.v_l]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (hk0.mul_int hi))
  have h3 := V.v.map_lt_add hM h1
  have h4 : -r - r ^ V.l + (V.l : C) * ((k : C) * r) = -(((2 : ℤ) : C) * r) := by
    rw [hpow]; push_cast; ring
  rw [h4, V.v.map_neg, V.v.map_mul, hv2, zero_add] at h3
  have h5 : ((-(d : ℤ) : ℤ) : C) = r * r := by push_cast; rw [← hr]; ring
  rw [h5, V.v.map_mul] at hvd
  have h6 : 0 < V.v r + V.v r := lt_of_lt_of_le h3 (le_add_of_nonneg_right h3.le)
  rw [hvd] at h6
  exact lt_irrefl _ h6

theorem labelling_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → N.cls V.l = PrimeClass.splitK → ∀ j : ℕ, ∃ (d : ℕ) (_ : NeZero d) (pos : RPl N.R → ℕ → RPl N.R) (Z : Finset (RPl N.R)), RF.IsReps (parAt N j d pos) Z ∧ Z.Nonempty ∧ Function.Bijective (fun x : Z × Fin 2 × ZMod d => tauSp N pl pos x.1.1 x.2.1 x.2.2) ∧ ∀ z g, FrobOrd V io ι (tauSp (d := d) N pl pos z g) := by
  intro E _ _ _ H lv c N pl hP la T io C _ _ V ι hE hl _ hcls j
  obtain ⟨φ, hφ⟩ := GlobalTheory.RowAt.exists_frob_all_embeddings E H lv c T io C V ι hE hP.galois hP.comm
  haveI : Inhabited (RPl N.R) := ⟨(false, 0)⟩
  have h2 : V.l ≠ 2 := by
    intro h
    unfold NumDatum.cls primeClass at hcls
    rw [if_pos (show V.l ∈ N.H.small from h ▸ Nat.mem_primeFactors.2 ⟨Nat.prime_two, N.H.two_dvd_QS, N.H.QS_pos.ne'⟩)] at hcls
    exact absurd hcls (by decide)
  have hj : jacobiSym (-(H.d : ℤ)) V.l = 1 := by
    rw [hP.d_eq]
    by_contra h
    unfold NumDatum.cls primeClass at hcls
    split_ifs at hcls
  have hfix : φ (H.rt : E) = H.rt := by
    have h1 : (φ (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      rw [← map_pow, rt_sq_field]; simp
    refine (sq_eq_sq_iff_eq_or_eq_neg.1 h1).resolve_right fun h => ?_
    let τ : E →+* ℂ := pl default
    have h3 : emA3 io ι (τ.comp (φ : E →+* E)) H.rt = -emA3 io ι τ H.rt := by
      have : embK c (τ.comp (φ : E →+* E)) H.rt = -embK c τ H.rt := by
        apply Subtype.ext
        rw [embK_coe]
        push_cast
        rw [embK_coe]
        simp [h]
      simp only [emA3, RingHom.comp_apply, this, map_neg]
    have h4 := hφ τ H.rt
    rw [h3] at h4
    refine not_MM_neg_sub_pow V H.d _ ?_ ?_ h2 hj h4
    · rw [← map_pow, H.rt_sq]; simp
    · exact ge_of_isIntegral V (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral H.rt))
  have hfixs : ∀ s : ℕ, (φ ^ s) (H.rt : E) = H.rt := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [pow_succ, AlgEquiv.mul_apply, hfix, ih]
  have hex : ∀ (z : RPl N.R) (s : ℕ), ∃ z', pl z' = (pl z).comp ((φ ^ s : E ≃ₐ[ℚ] E) : E →+* E) := by
    intro z s
    refine (hP.psi _).1 ?_
    have : InPsi H (pl z) := (hP.psi _).2 ⟨z, rfl⟩
    unfold InPsi at this ⊢
    change pl z ((φ ^ s) (H.rt : E)) = H.rt0
    rw [hfixs]; exact this
  choose pos hpos using hex
  haveI : NeZero (orderOf φ) := ⟨(orderOf_pos φ).ne'⟩
  have h0 : ∀ z, pos z 0 = z := fun z => hP.inj (by rw [hpos]; ext x; simp)
  have hadd : ∀ z s t, pos (pos z s) t = pos z (s + t) := fun z s t =>
    hP.inj (by rw [hpos, hpos, hpos]; ext x; simp [pow_add])
  have hfree : ∀ z s t, pos z s = pos z t ↔ s ≡ t [MOD orderOf φ] := by
    intro z s t
    rw [← pow_eq_pow_iff_modEq, ← hP.inj.eq_iff, hpos, hpos]
    constructor
    · intro h
      ext x
      exact (pl z).injective (RingHom.congr_fun h x)
    · intro h; rw [h]
  obtain ⟨Z, hZ⟩ := exists_reps (orderOf φ) pos h0 hadd hfree
  have hin : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
  have hnc : ∀ z z', pl z ≠ ComplexEmbedding.conjugate (pl z') := fun z z' h =>
    (inPsi_conj_iff H _).1 (h ▸ hin z) (hin z')
  have huniq : ∀ (z z' : Z) (s s' : ZMod (orderOf φ)), pl (pos z s.val) = pl (pos z' s'.val) → z = z' ∧ s = s' := by
    intro z z' s s' h
    have := (hZ (pos z' s'.val)).unique (y₁ := (z.1, s)) (y₂ := (z'.1, s')) ⟨z.2, hP.inj h⟩ ⟨z'.2, rfl⟩
    exact ⟨Subtype.ext (congrArg Prod.fst this), congrArg Prod.snd this⟩
  refine ⟨orderOf φ, inferInstance, pos, Z, hZ, ?_, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨p, hp, -⟩ := hZ default
    exact ⟨p.1, hp.1⟩
  · rintro ⟨z, g, s⟩ ⟨z', g', s'⟩ h
    simp only [tauSp] at h
    split_ifs at h with hg hg' hg'
    · obtain ⟨rfl, rfl⟩ := huniq _ _ _ _ h
      rw [hg, hg']
    · exact absurd h (hnc _ _)
    · exact absurd h.symm (hnc _ _)
    · obtain ⟨rfl, rfl⟩ := huniq _ _ _ _ (star_injective h)
      have : g = g' := by omega
      rw [this]
  · intro τ
    by_cases hτ : InPsi H τ
    · obtain ⟨z', rfl⟩ := (hP.psi _).1 hτ
      obtain ⟨p, hp, -⟩ := hZ z'
      exact ⟨(⟨p.1, hp.1⟩, 0, p.2), by simp [tauSp, hp.2]⟩
    · obtain ⟨z', hz'⟩ := (hP.psi _).1 ((inPsi_conj_iff H τ).2 hτ)
      obtain ⟨p, hp, -⟩ := hZ z'
      refine ⟨(⟨p.1, hp.1⟩, 1, p.2), ?_⟩
      simp only [tauSp, hp.2, hz', one_ne_zero, if_false]
      exact star_star τ
  · intro z g s x
    have h1 : pos z (s + 1).val = pos z (s.val + 1) := by
      rw [hfree, ← ZMod.natCast_eq_natCast_iff]
      simp
    have h3 : pl (pos z (s + 1).val) = (pl (pos z s.val)).comp (φ : E →+* E) := by
      rw [h1, hpos, hpos]; ext y; simp [pow_succ]
    have h4 : tauSp (d := orderOf φ) N pl pos z g (s + 1) = (tauSp (d := orderOf φ) N pl pos z g s).comp (φ : E →+* E) := by
      unfold tauSp
      split_ifs
      · exact h3
      · rw [h3]; rfl
    rw [h4]
    exact hφ _ x

end GlobalTheory.LabSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthAtTwoOfUnscaledDepthBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem leafDepthTwo_of_unscaled_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs) (Nd : NumDatum), (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) → O.T = ((Dd.Q.T : ℕ) : ℝ) → (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O → ContentEqualsDatumContent N Nd ι → TiePrimes O Nd → (∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∈ O.sm → ∀ j, ∃ B : ℝ, O.T * B ≤ O.sC j ∧ nuWAt (Xo := Xo (ι j)) (c := c) Dd la (ι j) ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal)) → LeafDepth2 N O := by
  intro E _ _ _ H l Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N Nd hE hσ hT hpr hsp hPg tF tP hB
  have hT0 : (0 : ℝ) ≤ O.T := by rw [hT]; positivity
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), plc v ∈ O.sm →
      (1 ≤ DepthTie.e1 c v ∧ 1 ≤ DepthTie.e2 c v ∧ ramw v = (DepthTie.e1 c v : ℤ) * (DepthTie.e2 c v : ℤ) ∧
        ∀ j, (O.E v j : ℤ) ≤ (DepthTie.e1 c v : ℤ) *
          ⌈(DepthTie.e2 c v : ℝ) * O.T * (DepthTie.nuT Xo c Dd ι v j + if plc v ∈ O.Bad then 1 else 0)⌉) →
      O.e0 v j ≤ O.sC j + O.T + 1 := by
    intro v j hv ⟨he1, he2, hram, hEv⟩
    have hbad : plc v ∈ O.Bad := by simp [OnObj.Bad, hv]
    have hEj := hEv j
    rw [if_pos hbad] at hEj
    have hR := rounding_condition_holds (DepthTie.e1 c v) (DepthTie.e2 c v) (O.T * (DepthTie.nuT Xo c Dd ι v j + 1))
      (O.E v j) he1 he2 (by rw [← mul_assoc]; exact hEj)
    have hramR : (ramw v : ℝ) = (DepthTie.e1 c v : ℝ) * (DepthTie.e2 c v : ℝ) := by simp [hram]
    have he2R : (1 : ℝ) ≤ DepthTie.e2 c v := by exact_mod_cast he2
    have hinv : 1 / (DepthTie.e2 c v : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact he2R
    have hs1 := GlobalTheory.RunDepth.sprime_nonneg_two E H l Dw Xo c Dd K Bs Df S P oc O ι hT hpr hσ hsp hPg v hv j
    obtain ⟨B, hTB, hν⟩ := hB (placeBelow (K := c.F) v) (by rw [DepthTie.resChar_below (F := c.F) v]; exact hv) j
    have hW : DepthTie.nuWT Xo c Dd ι v j ≤ B := by
      have h0 : (0 : EReal) ≤ nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j) := le_max_left _ _
      have ht := EReal.toReal_le_toReal hν (ne_bot_of_le_ne_bot EReal.zero_ne_bot h0) (EReal.coe_ne_top _)
      rw [EReal.toReal_coe] at ht
      unfold DepthTie.nuWT
      rw [div_le_iff₀ (by linarith), mul_comm]
      exact ht
    have hTW := mul_le_mul_of_nonneg_left hW hT0
    have he0 : O.e0 v j = (O.E v j : ℝ) / ((DepthTie.e1 c v : ℝ) * (DepthTie.e2 c v : ℝ)) -
        (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) := by
      unfold OnObj.e0
      rw [sub_div, hramR]
    unfold DepthTie.s1T DepthTie.sWT at hs1
    rw [he0]
    nlinarith
  intro w hw h2 j
  obtain ⟨h1, h1'⟩ := DepthTie.tieE Xo c Dd O ι hE hT hpr w hw
  exact ⟨key w j h2 h1, key (conjPl w) j (by rw [plc_conjPl]; exact h2) h1', content_zero_at_small_primes N O Nd ι hPg tF tP w h2 j⟩

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicElementOfMarkedComponentLatticeStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_element_of_marked_component_lattice : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif Xo σ' ty), IsTypeFn H Dw.p Dw.q ty → ∀ (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (i : Fin F.n) (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] X.Λ) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), ModelW V hr X → (∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → LatEmb V io → FormPlus V io → ∃ h : GA D V, Marked V hr io l X.Λ (fun a => (φ (F.t i a) : Fin r → D.host.E)) h := by
  first | exact @GlobalTheory.ShortMove.exists_marked_of_component | exact GlobalTheory.ShortMove.exists_marked_of_component | (intros; apply GlobalTheory.ShortMove.exists_marked_of_component <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicUnitaryOfLatticeIsometriesStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_unitary_of_lattice_isometries : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V io → FormPlus V io → ∀ s : Sim Dw, (∀ n, s.ν n = 1) → ∃ κ : GA D V, latGHat V κ = latGHat V 1 ∧ ∀ N : ℕ, 0 < N → ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s.f N a)) + N • w := by
  first | exact @GlobalTheory.ShortMove.exists_adelic_of_isometry | exact GlobalTheory.ShortMove.exists_adelic_of_isometry | (intros; apply GlobalTheory.ShortMove.exists_adelic_of_isometry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharacterGermValuationEqColumnTypedStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_characterGerm_valuation_eq_columnTyped : ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (B : FB O d OE) (h : PS C 2 d), B.IsCanonGauge C h → ∀ (w0 : OE) (k n : ℕ) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) [Fintype (Letter Ty r n)] (σ : Ty → (OE →+* O)) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → O), (∀ ℓ a, (linPart (B.A.act a)).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → (∀ τ, ∃ a0, IsUnit (σ τ a0 - σ τ (star a0))) → (∀ x : O, x ≠ 0 → ∃ N : ℕ, v (N : C) < v (algebraMap O C x) ∧ ∀ τ, ∃ a : OE, star a * a = (N : OE) ∧ v (algebraMap O C (σ τ a - 1)) < v (algebraMap O C x)) → ∀ (ty : Fin n → Ty) (P : MvPolynomial (Letter Ty r n) O), (∀ mo ∈ P.support, ∀ ℓ, mo ℓ ≠ 0 → ℓ.1 = ty ℓ.2.2) → ∀ χ : Fin n → PS O 1 d, (∀ b, IsCh B.G.F (χ b)) → MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P ≠ 0 → ∃ f : PS O n d, v (nabValN B C h w0 k (MvPowerSeries.map (algebraMap O C) f) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun (ℓ : Letter Ty r n) i => algebraMap O C (u ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map (algebraMap O C) P)) = v (algebraMap O C (MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P)) := by
  first | exact @GlobalTheory.CharValue.exists_germ_valuation_eq | exact GlobalTheory.CharValue.exists_germ_valuation_eq | (intros; apply GlobalTheory.CharValue.exists_germ_valuation_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsClosedCompleteFieldOverPlaceStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedComplete_field_over_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∃ (C : Type) (_ : Field C) (_ : CharZero C) (V : VF C) (ι : T.Fr →+* C), V.l = resCharOf la ∧ EmbOK T V ι ∧ IsAlgClosed C ∧ (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) ∧ (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) ∧ (∀ m : ℕ, ¬ resCharOf la ∣ m → V.v (m : C) = 0) ∧ ∀ (y : IntFr Xo c T io) (C3 : IntChart T io y) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C3 e k a n → (ν : EReal) ≤ nuLocC C3 (eOf T V) k a n := by
  first | exact @GlobalTheory.PlaceClosedField.exists_closed_field_over_place | exact GlobalTheory.PlaceClosedField.exists_closed_field_over_place | (intros; apply GlobalTheory.PlaceClosedField.exists_closed_field_over_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHighestWeightIrreducibleUnitaryRepUStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highestWeight_irreducible_unitaryRep_U : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π → (∀ S : Submodule ℂ W, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∃ u, PI.UpqRep.IsHCTypeU k u π := by
  first | exact @GlobalTheory.UnitaryHighestWeight.exists_isHCTypeU | exact GlobalTheory.UnitaryHighestWeight.exists_isHCTypeU | (intros; apply GlobalTheory.UnitaryHighestWeight.exists_isHCTypeU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIdempotentFrobeniusOrbitUnramifiedStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_frobeniusOrbit_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), FrobOrd V io ι tau → ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (tau a) ε - 1)) ∧ ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (tau a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y := by
  first | exact @GlobalTheory.exists_idempotent_of_unramified_place | exact GlobalTheory.exists_idempotent_of_unramified_place | (intros; apply GlobalTheory.exists_idempotent_of_unramified_place <;> assumption)
end

